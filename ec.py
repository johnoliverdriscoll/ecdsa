from collections import namedtuple
from libnum import invmod
from random import SystemRandom

Point = namedtuple('Point', 'x y')

class EllipticCurve(object):

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

    def point_add(self, P, Q):
        """ Return P + Q """
        if P == EllipticCurve.inf:
            return Q
        if Q == EllipticCurve.inf:
            return P
        if P.x == Q.x:
            if (P.y + Q.y) % self.p == 0:
                return EllipticCurve.inf
            return self.point_double(P)
        s = ((Q.y - P.y) * invmod(Q.x - P.x, self.p)) % self.p
        x = (s * s - P.x - Q.x) % self.p
        y = (s * (P.x - x) - P.y) % self.p
        return Point(x, y)

    def point_double(self, P):
        """ Return P + P """
        if P == EllipticCurve.inf:
            return P
        s = ((3 * P.x * P.x + self.a) * invmod(2 * P.y, self.p)) % self.p
        x = (s * s - 2 * P.x) % self.p
        y = (s * (P.x - x) - P.y) % self.p
        return Point(x, y)

    def point_multiply(self, n, P):
        """ Return n * P """
        if n == 0 or P == EllipticCurve.inf:
            return EllipticCurve.inf
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

    def public_key(self, d, compressed=True):
        """ Return serialized public key """
        P = self.point_multiply(d, self.G)
        if compressed:
            if not P.y % 2:
                return '02' + format(P.x, '02x')
            return '03' + format(P.x, '02x')
        return '04' + format(P.x, '02x') + format(P.y, '02')

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

    def sign(self, d, e):
        """
        Returns a DER serialized signature of message e using private key d.
        d is a private key (integer).
        e is an encoded message (integer).
        """
        z = self.shrink_message(e)
        k, r = None, None
        while True:
            k = self.random.randint(1, self.n - 1)
            P = self.point_multiply(k, self.G)
            r = P.x % self.n
            if r == 0:
                continue
            s = invmod(k, self.n) * (z + (r * d) % self.n) % self.n
            if s != 0:
                break
        # Byte sizes of r, s
        rBn = (r.bit_length() + 7) // 8
        sBn = (s.bit_length() + 7) // 8
        # Byte sizes of components and sequence bytes
        mBn = 4 + rBn + sBn
        # Numeric representation of the DER serialized sig
        sig = [ 0x30, # DER sequence byte
                mBn,  # bytes in message
                0x02, # DER integer byte
                rBn,  # bytes in r
                r,    # r value
                0x02, # DER integer byte
                sBn,  # bytes in s
                s ]   # s value
        # Return a hex string of all the sig bytes
        return ''.join([
            '0' + f if len(f) % 2 else f \
            for f in [format(x, '02x') for x in sig]])

    def verify(self, pkey, e, sig):
        """
        Verifies a message e was signed by the owner of public key pkey.
        Returns True if e was signed by the owner of pkey.
        Raises AssertionError if the signature is invalid.
        pkey is a serialized public key.
        e is the encoded message.
        sig is the DER serialized message.
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
        if pkey[:2] == '04':
            P = Point(int(pkey[2:66], 16), int(pkey[66:]))
        else:
            y_parity = int(pkey[:2]) - 2
            x = int(pkey[2:], 16)
            a = (pow_mod(x, 3, self.p) + self.b) % self.p
            y = pow_mod(a, (self.p + 1) // 4, self.p)
            if y % 2 != y_parity:
                y = -y % self.p
            P = Point(x, y)
        # P must not be point at infinity
        assert P != EllipticCurve.inf
        # P must lie on the curve
        y = P.y * P.y
        x = P.x * P.x * P.x + self.a * P.x + self.b
        assert y % self.p == x % self.p
        # Now unmarshall the signature
        assert sig[:2] == '30' # DER SEQUENCE byte
        mBn = int(sig[2:4], 16) # bytes in message
        assert sig[4:6] == '02' # DER INTEGER byte
        rBn = int(sig[6:8], 16) # bytes in r
        r = int(sig[8:8 + rBn * 2], 16) # r value
        assert sig[8 + rBn * 2:8 + rBn * 2 + 2] == '02' # DER INTEGER byte
        sBn = int(sig[8 + rBn * 2 + 2:8 + rBn * 2 + 4], 16) # bytes in s
        assert sBn == len(sig[8 + rBn * 2 + 4:4 + mBn * 2]) // 2
        s = int(sig[8 + rBn * 2 + 4:4 + mBn * 2], 16) # s value
        # Now we have (r,s) and can verify
        z = self.shrink_message(e)
        w = invmod(s, self.n)
        U1 = self.point_multiply(z * w % self.n, self.G)
        U2 = self.point_multiply(r * w % self.n, P)
        R = self.point_add(U1, U2)
        assert r == R.x
        return True

secp256k1 = EllipticCurve(
    a = 0,
    b = 7,
    p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F,
    n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141,
    G = Point(
    x = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
    y = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8))

if __name__ == '__main__':

    """ Use secp256k1 to sign and verify a message """

    from hashlib import sha256
    from sys import stdout

    E = secp256k1
    k = E.random.randint(1, E.n - 1)
    pubk = E.public_key(k)
    m = 'TOO MANY SECRETS'
    e = int(sha256(sha256(m).digest()).hexdigest(), 16)
    sig = E.sign(k, e)
    err = None
    print "k      : " + format(k, '02x')
    print "pubk   : " + pubk
    print 'm      : "' + m + '"'
    print "e=H(m) : " + format(e, '02x')
    print "sig    : " + sig[:70]
    print "       : " + sig[70:]
    stdout.write("verify : ")
    E.verify(pubk, e, sig)
    print "True"
