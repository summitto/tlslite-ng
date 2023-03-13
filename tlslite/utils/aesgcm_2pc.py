# Author: Google
# See the LICENSE file for legal information regarding use of this file.

# GCM derived from Go's implementation in crypto/cipher.
#
# https://golang.org/src/crypto/cipher/gcm.go

# GCM works over elements of the field GF(2^128), each of which is a 128-bit
# polynomial. Throughout this implementation, polynomials are represented as
# Python integers with the low-order terms at the most significant bits. So a
# 128-bit polynomial is an integer from 0 to 2^128-1 with the most significant
# bit representing the x^0 term and the least significant bit representing the
# x^127 term. This bit reversal also applies to polynomials used as indices in a
# look-up table.

from __future__ import division
from tlslite.utils import python_aes
from .constanttime import ct_compare_digest
from .cryptomath import bytesToNumber, numberToByteArray

def reverseHex(hexString):
    asBits = bin(int(hexString, 16))[2:].zfill(128)
    result = hex(int(asBits[::-1], 2))[2:]
    return result

class AESGCM_2PC(object):
    """
    AES-GCM implementation. Note: this implementation does not attempt
    to be side-channel resistant. It's also rather slow.
    """

    def __init__(self, key, implementation, rawAesEncrypt, masked_powers_of_h):
        self.isBlockCipher = False
        self.isAEAD = True
        self.nonceLength = 12
        self.tagLength = 16
        self.implementation = implementation
        if len(key) == 16:
            self.name = "aes128gcm"
        elif len(key) == 32:
            self.name = "aes256gcm"
        else:
            raise AssertionError()
        self.key = key

        self._rawAesEncrypt = rawAesEncrypt
        self._ctr = python_aes.new(self.key, 6, bytearray(b'\x00' * 16))

        self.h_multiplications = 0

        # The GCM key is AES(0).
        h_bytes = self._rawAesEncrypt(bytearray(16))
        h = bytesToNumber(h_bytes)

        self._productTable = [0] * 16
        self._genProductTable(self._productTable, h)

        h_table = []
        for i in range(len(masked_powers_of_h)):
            # print(masked_powers_of_h[i])
            h_table.append(bytesToNumber(bytes.fromhex(masked_powers_of_h[i])))
        self._productTables = []
        for i in range(len(h_table)):
            self._productTables.append([0] * 16)
            self._genProductTable(self._productTables[i], h_table[i])

    # Pre-compute all 4-bit multiples of h. Note that bits are reversed
    # because our polynomial representation places low-order terms at the
    # most significant bit. Thus x^0 * h = h is at index 0b1000 = 8 and
    # x^1 * h is at index 0b0100 = 4.
    def _genProductTable(self, productTable, h):
        productTable[self._reverseBits(1)] = h
        for i in range(2, 16, 2):
            productTable[self._reverseBits(i)] = \
                self._gcmShift(productTable[self._reverseBits(i//2)])
            productTable[self._reverseBits(i+1)] = \
                self._gcmAdd(productTable[self._reverseBits(i)], h)

    def _auth(self, ciphertext, ad, tagMask):
        y = 0
        y = self._update(y, ad, self._productTable)
        y = self._update(y, ciphertext, self._productTable)
        y ^= (len(ad) << (3 + 64)) | (len(ciphertext) << 3)
        y = self._mul(y, self._productTable)
        y ^= bytesToNumber(tagMask)
        self.h_multiplications = 0
        return numberToByteArray(y, 16)

    def _ghash(self, ciphertext, ad):
        y = 0
        chunks = self._chunk(ad)
        chunks += self._chunk(ciphertext)
        chunks.append((len(ad) << (3 + 64)) | (len(ciphertext) << 3))
        for i in range(len(chunks)):
            y ^= self._mul(chunks[i], self._productTables[len(chunks) - 1 - i])
        self.h_multiplications = 0
        return numberToByteArray(y, 16)
    
    def _auth2PC(self, counterparty_share, tag_mask_share, ghash_share, tag):
        return tag == counterparty_share ^ tag_mask_share ^ ghash_share

    def _authTest(self, ciphertext, ad, tagMask):
        y = 0
        chunks = self._chunk(ad)
        chunks += self._chunk(ciphertext)
        chunks.append((len(ad) << (3 + 64)) | (len(ciphertext) << 3))
        for i in range(len(chunks)):
            y ^= self._mul(chunks[i], self._productTables[len(chunks) - 1 - i])
        y ^= bytesToNumber(tagMask)
        self.h_multiplications = 0
        return numberToByteArray(y, 16)

    def _authTestSplit(self, ciphertext, ad, tagMask):
        y1 = 0
        y2 = 0
        chunks = self._chunk(ad)
        chunks += self._chunk(ciphertext)
        chunks.append((len(ad) << (3 + 64)) | (len(ciphertext) << 3))
        for i in range(len(chunks)):
            y1 ^= self._mul(chunks[i], self._productTables1[len(chunks) - 1 - i])
        for i in range(len(chunks)):
            y2 ^= self._mul(chunks[i], self._productTables2[len(chunks) - 1 - i])
        ysum = y1 ^ y2
        ysum ^= bytesToNumber(tagMask)
        self.h_multiplications = 0
        return numberToByteArray(ysum, 16)

    def _chunk(self, data):
        chunks = []
        for i in range(0, len(data) // 16):
            chunks.append(bytesToNumber(data[16*i:16*i+16]))
        extra = len(data) % 16
        if extra != 0:
            block = bytearray(16)
            block[:extra] = data[-extra:]
            chunks.append(bytesToNumber(block))
        return chunks

    def _update(self, y, data, productTable):
        for i in range(0, len(data) // 16):
            y ^= bytesToNumber(data[16*i:16*i+16])
            y = self._mul(y, productTable)
        extra = len(data) % 16
        if extra != 0:
            block = bytearray(16)
            block[:extra] = data[-extra:]
            y ^= bytesToNumber(block)
            y = self._mul(y, productTable)
        return y

    def _mul(self, y, productTable):
        """ Returns y*H, where H is the GCM key. """
        ret = 0
        y_copy = y
        ret_copy = 0
        self.h_multiplications += 1

        #  # Multiply H by y 4 bits at a time, starting with the highest power
        #  # terms.
        #  for i in range(0, 128, 4):
        #      # Multiply by x^4. The reduction for the top four terms is
        #      # precomputed.
        #      retHigh = ret & 0xf
        #      ret >>= 4
        #      ret ^= (AESGCM._gcmReductionTable[retHigh] << (128-16))

        #      # Add in y' * H where y' are the next four terms of y, shifted down
        #      # to the x^0..x^4. This is one of the pre-computed multiples of
        #      # H. The multiplication by x^4 shifts them back into place.
        #      ret ^= self._productTable[y & 0xf]
        #      y >>= 4
        #  assert y == 0

        # Multiply H by y 1 bit at a time, starting with the highest power
        # terms.
        for i in range(0, 128, 1):
            retHigh = ret_copy & 1
            ret_copy >>= 1
            ret_copy ^= (AESGCM_2PC._gcmReductionTableAlt[retHigh] << (128-8))
            ret_copy ^= productTable[self._reverseBits(y_copy & 1)] # we index 0 or 8
            y_copy >>= 1
        assert y_copy == 0

        return ret_copy

    def seal(self, nonce, plaintext, data):
        """
        Encrypts and authenticates plaintext using nonce and data. Returns the
        ciphertext, consisting of the encrypted plaintext and tag concatenated.
        """

        if len(nonce) != 12:
            raise ValueError("Bad nonce length")

        # The initial counter value is the nonce, followed by a 32-bit counter
        # that starts at 1. It's used to compute the tag mask.
        counter = bytearray(16)
        counter[:12] = nonce
        counter[-1] = 1
        tagMask = self._rawAesEncrypt(counter)

        # The counter starts at 2 for the actual encryption.
        counter[-1] = 2
        self._ctr.counter = counter
        ciphertext = self._ctr.encrypt(plaintext)

        tag = self._auth(ciphertext, data, tagMask)
        print("tag:",tag)

        return ciphertext + tag

    def open(self, nonce, ciphertext, data):
        """
        Decrypts and authenticates ciphertext using nonce and data. If the
        tag is valid, the plaintext is returned. If the tag is invalid,
        returns None.
        """

        if len(nonce) != 12:
            raise ValueError("Bad nonce length")
        if len(ciphertext) < 16:
            return None

        tag = ciphertext[-16:]
        ciphertext = ciphertext[:-16]

        # The initial counter value is the nonce, followed by a 32-bit counter
        # that starts at 1. It's used to compute the tag mask.
        counter = bytearray(16)
        counter[:12] = nonce
        counter[-1] = 1
        tagMask = self._rawAesEncrypt(counter)

        if not ct_compare_digest(tag, self._auth(ciphertext, data, tagMask)):
            return None

        # The counter starts at 2 for the actual decryption.
        counter[-1] = 2
        self._ctr.counter = counter
        return self._ctr.decrypt(ciphertext)

    @staticmethod
    def _reverseBits(i):
        assert i < 16
        i = ((i << 2) & 0xc) | ((i >> 2) & 0x3)
        i = ((i << 1) & 0xa) | ((i >> 1) & 0x5)
        return i

    @staticmethod
    def _gcmAdd(x, y):
        return x ^ y

    @staticmethod
    def _gcmShift(x):
        # Multiplying by x is a right shift, due to bit order.
        highTermSet = x & 1
        x >>= 1
        if highTermSet:
            # The x^127 term was shifted up to x^128, so subtract a 1+x+x^2+x^7
            # term. This is 0b11100001 or 0xe1 when represented as an 8-bit
            # polynomial.
            x ^= 0xe1 << (128-8)
        return x

    @staticmethod
    def _inc32(counter):
        for i in range(len(counter)-1, len(counter)-5, -1):
            counter[i] = (counter[i] + 1) % 256
            if counter[i] != 0:
                break
        return counter

    # _gcmReductionTable[i] is i * (1+x+x^2+x^7) for all 4-bit polynomials i. The
    # result is stored as a 16-bit polynomial. This is used in the reduction step to
    # multiply elements of GF(2^128) by x^4.
    _gcmReductionTable = [
        0x0000, 0x1c20, 0x3840, 0x2460, 0x7080, 0x6ca0, 0x48c0, 0x54e0,
        0xe100, 0xfd20, 0xd940, 0xc560, 0x9180, 0x8da0, 0xa9c0, 0xb5e0,
    ]
    _gcmReductionTableAlt = [0x00, 0xe1]
