from collections import namedtuple
from random import SystemRandom

Point = namedtuple('Point', 'x y')

class ECDSA(object):

    inf = Point(None, None)

    def __init__(self, a, b, p, G = None, n = None):
        """
        a, b, p are the definition of the curve.
        G is the generator point.
        n is the integer order.
        """
        self.a = a
        self.b = b
        self.p = p
        self.n = n
        self.G = G
        self.random = SystemRandom()

    def hex(self, n, l = None):
        assert type(n) in [long, int]
        if l is None:
            l = (n.bit_length() + 7) // 8
        s = format(n, '0%dx' % (l * 2))
        assert len(s) == l * 2
        return s

    def point_add(self, P, Q):
        """ Return P + Q """
        if P == ECDSA.inf:
            return Q
        if Q == ECDSA.inf:
            return P
        if P.x == Q.x:
            if (P.y + Q.y) % self.p == 0:
                return ECDSA.inf
            return self.point_double(P)
        s_1 = ECDSA.invmod(Q.x - P.x, self.p)
        s = ((Q.y - P.y) * s_1) % self.p
        x = (s * s - P.x - Q.x) % self.p
        y = (s * (P.x - x) - P.y) % self.p
        return Point(x, y)

    def point_double(self, P):
        """ Return P + P """
        if P == ECDSA.inf:
            return P
        s_1 = ECDSA.invmod(2 * P.y, self.p)
        s = ((3 * P.x * P.x + self.a) * s_1) % self.p
        x = (s * s - 2 * P.x) % self.p
        y = (s * (P.x - x) - P.y) % self.p
        return Point(x, y)

    def point_multiply(self, n, P):
        """ Return n * P """
        if n == 0 or P == ECDSA.inf:
            return ECDSA.inf
        assert n > 0
        e = 3 * (n % self.n)
        inverse = Point(P.x, -P.y)
        R = Point(P.x, P.y)
        for i in [1 << i for i in reversed(range(1, e.bit_length() - 1))]:
            R = self.point_double(R)
            if e & i and not n & i:
                R = self.point_add(R, P)
            if not e & i and n & i:
                R = self.point_add(R, inverse)
        return R

    def private_key(self, randint = None):
        """ Returns a random number """
        if randint is None:
            randint = self.random.randint
        return randint(1, self.n - 1)

    def public_key(self, d, compressed=True):
        """ Return serialized public key """
        P = self.point_multiply(d, self.G)
        if compressed:
            return ('03' if P.y % 2 else '02') + self.hex(P.x, 32)
        return '04' + self.hex(P.x, 32) + self.hex(P.y, 32)

    def shrink_message(self, e):
        """
        Returns leftmost n.bit_length() bits of e.
        This is used to produce z from e, where e
        can be greater, but not longer in bits, to
        the intereger order of the curve.
        """
        en = e.bit_length()
        Ln = self.n.bit_length()
        z = e >> (en - Ln) if en > Ln else e
        assert z.bit_length() <= Ln
        return z

    def der_int(self, r):
        assert r >= 0
        h = self.hex(r)
        if int(h[0:2], 16) <= 0x7f:
            return h
        return "00" + h

    def sign(self, d, e, randint = None):
        """
        Returns a DER serialized signature of message e using private key d.
        d is a private key (integer).
        e is an encoded message (integer).
        """
        z = self.shrink_message(e)
        r, s = None, None
        if randint is None:
            randint = self.random.randint
        while True:
            k = randint(1, self.n - 1)
            P = self.point_multiply(k, self.G)
            r = P.x % self.n
            if r == 0:
                continue
            k_1 = ECDSA.invmod(k, self.n)
            s = k_1 * (z + r * d) % self.n
            if s == 0:
                continue
            break
        # Byte sizes of r, s
        r = self.der_int(r)
        s = self.der_int(s)
        num_bytes_in_r = len(r) // 2
        num_bytes_in_s = len(s) // 2
        # Byte sizes of components and sequence bytes
        num_bytes_in_seq = 4 + num_bytes_in_r + num_bytes_in_s
        # DER sig sequence
        return ''.join([
            "30", # DER sequence byte
            self.hex(num_bytes_in_seq),
            "02", # DER integer byte
            self.hex(num_bytes_in_r),
            r,
            "02", # DER integer byte
            self.hex(num_bytes_in_s),
            s
        ])

    def verify(self, pubk, e, sig):
        """
        Verifies a message e was signed by the owner of public key pubk.
        Returns True if e was signed by the owner of pkey.
        Raises AssertionError if the signature is invalid.
        pubk is a serialized public key.
        e is the encoded message.
        sig is the DER serialized signature.
        """
        # First we define modular exponent, which is
        # used to calculate the y from a compressed
        # public key.
        # This only works for curves with an integer
        # order n that is congruent to 3 mod 4.
        def pow_mod(x, y, z):
            n = 1
            while y:
                if y & 1:
                    n = n * x % z
                y >>= 1
                x = x * x % z
            return n
        # Now unmarshall the public key
        P = Point(None, None)
        if pubk[:2] == '04':
            P = Point(int(pubk[2:66], 16), int(pubk[66:]))
        else:
            y_parity = int(pubk[:2]) - 2
            assert y_parity in [0, 1]
            x = int(pubk[2:], 16)
            a = (pow_mod(x, 3, self.p) + self.b) % self.p
            y = pow_mod(a, (self.p + 1) // 4, self.p)
            if y % 2 != y_parity:
                y = -y % self.p
            P = Point(x, y)
        # P must not be point at infinity
        assert P != ECDSA.inf
        # P must lie on the curve
        y = P.y * P.y
        x = P.x * P.x * P.x + self.a * P.x + self.b
        assert y % self.p == x % self.p
        # Now unmarshall the signature
        # DER SEQUENCE byte
        a, b = 0, 2
        assert sig[a:b] == '30'
        a, b = b, b + 2
        num_bytes_in_seq = int(sig[a:b], 16)
         # DER INTEGER byte
        a, b = b, b + 2
        assert sig[a:b] == '02'
        a, b = b, b + 2
        num_bytes_in_r = int(sig[a:b], 16)
        a, b = b, b + num_bytes_in_r * 2
        r_str = sig[a:b]
        r = int(r_str, 16)
        assert r_str == self.der_int(r)
         # DER INTEGER byte
        a, b = b, b + 2
        assert sig[a:b] == '02'
        a, b = b, b + 2
        num_bytes_in_s = int(sig[a:b], 16)
        assert len(sig) == b + num_bytes_in_s * 2
        s_str = sig[b:]
        s = int(s_str, 16)
        assert s_str == self.der_int(s)
        # Now we have (r,s) and can verify
        z = self.shrink_message(e)
        w = ECDSA.invmod(s, self.n)
        U1 = self.point_multiply(z * w % self.n, self.G)
        U2 = self.point_multiply(r * w % self.n, P)
        R = self.point_add(U1, U2)
        assert r == R.x
        return True

    @staticmethod
    def extended_gcd(a, b):
        """ Extended GCD needed to compute modular inverse """
        l, r = abs(a), abs(b)
        x, lx, y, ly = 0, 1, 1, 0
        while r:
            l, (q, r) = r, divmod(l, r)
            x, lx = lx - q * x, x
            y, ly = ly - q * y, y
        return l, lx * (-1 if a < 0 else 1), ly * (-1 if b < 0 else 1)

    @staticmethod
    def invmod(a, m):
        """ Compute inverse of a mod m """
        g, x, y = ECDSA.extended_gcd(a, m)
        if g != 1:
            raise ValueError
        return x % m

secp256k1 = ECDSA(
    a = 0,
    b = 7,
    p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F,
    n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141,
    G = Point(
    x = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
    y = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8))

if __name__ == '__main__':

    from hashlib import sha256
    from sys import stdout
    from subprocess import Popen, PIPE
    from os import remove
    from array import array

    E = secp256k1
    m = "TOO MANY SECRETS"
    e = int(sha256(m).hexdigest(), 16)

    print 'm       : "' + m + '"'
    print "H       : " + str(sha256)
    print "e=H(m)  : " + E.hex(e)
    print "z=Ln(e) : " + E.hex(E.shrink_message(e))
    print

    print "ecdsa.py sanity check"
    for i in range(5):
        k = E.private_key()
        print "k    : " + E.hex(k)
        pubk = E.public_key(k)
        print "pubk : " + pubk
        sig = E.sign(k, e)
        print "sig  : " + sig[:64]
        print "     : " + sig[64:128]
        print "     : " + sig[128:]
        E.verify(pubk, e, sig)
    print

    for i in range(5):
        # Generate a key
        c = "openssl ecparam -name secp256k1 -genkey"
        p = Popen(c.split(' '), stdout=PIPE, stderr=PIPE)
        k_pem, err = p.communicate()
        if p.returncode:
            raise Exception(err)
        # Convert it to DER
        c = "openssl ec -outform der"
        p = Popen(c.split(' '), stdin=PIPE, stdout=PIPE, stderr=PIPE)
        k_der, err = p.communicate(k_pem)
        if p.returncode:
            raise Exception(err)
        k_len = int(k_der[6].encode('hex'), 16)
        k = int(k_der[7:7+k_len].encode('hex'), 16)
        # Derive public key
        c = "openssl ec -pubout -conv_form compressed -outform der"
        p = Popen(c.split(' '), stdin=PIPE, stdout=PIPE, stderr=PIPE)
        pubk_der, err = p.communicate(k_pem)
        if p.returncode:
            raise Exception(err)
        pubk = pubk_der[-33:].encode('hex')
        assert pubk == E.public_key(k)
        message_file = open('message.txt', 'wb')
        message_file.write(m)
        message_file.close()
        try:
            print "verify openssl signature with ecdsa.py"
            print "k    : " + E.hex(k)
            print "pubk : " + pubk
            for j in range(5):
                c = "openssl dgst -sha256 -hex -sign /dev/stdin message.txt"
                p = Popen(c.split(' '), stdin=PIPE, stdout=PIPE, stderr=PIPE)
                sig_der, err = p.communicate(k_pem)
                if p.returncode:
                    raise Exception(err)
                sig = sig_der.split(' ')[1][:-1]
                print "sig  : " + sig[:64]
                print "     : " + sig[64:128]
                print "     : " + sig[128:]
                E.verify(pubk, e, sig)
            print
            print "verify ecdsa.py signature with openssl"
            print "k    : " + E.hex(k)
            print "pubk : " + pubk
            for j in range(5):
                sig = E.sign(k, e)
                sig_bytes = [int(sig[i:i+2], 16) \
                             for i in range(0, len(sig), 2)]
                sig_file = open('signature.der', 'wb')
                array('B', sig_bytes).tofile(sig_file)
                sig_file.close()
                print "sig  : " + sig[:64]
                print "     : " + sig[64:128]
                print "     : " + sig[128:]
                c = "openssl dgst -sha256 -prverify /dev/stdin " + \
                    "-signature signature.der message.txt"
                p = Popen(c.split(' '), stdin=PIPE, stdout=PIPE, stderr=PIPE)
                out, err = p.communicate(k_pem)
                if p.returncode:
                    raise Exception(err if err else out)
            print
        finally:
            remove('message.txt')
            remove('signature.der')
