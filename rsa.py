#!/usr/bin/env python

import argparse
import copy
import math
import pickle
import random
from itertools import combinations
from base64 import b64encode
from pyasn1.codec.der.encoder import encode as der_encoder
from rsa_key import RSAPrivateKey, RSAPublicKey
from pyasn1.codec.native.decoder import decode
from urllib.request import Request, urlopen
from time import sleep

base_url = "https://www.random.org/integers/?num=1&min={0}&max={1}&col=1&base=10&format=plain&rnd=new"


# Was actually going to use Random.org's guassian generator for noise generation but figured that due to 
def get_random_number(lower=0, upper=1000000000):
    link = base_url.format(lower, upper)
    request = Request(link)
    request.add_header("User-agent", "pichu@pikachu.raichu")
    response = urlopen(request).read()
    randNum = float('-inf')
    for num in response.splitlines():
        return int(num)

def euclid(a, b):
    """returns the Greatest Common Divisor of a and b"""
    a = abs(a)
    b = abs(b)
    if a < b:
        a, b = b, a
    while b != 0:
        a, b = b, a % b
    return a


def coPrime(l):
    """returns 'True' if the values in the list L are all co-prime
       otherwise, it returns 'False'. """
    for i, j in combinations(l, 2):
        if euclid(i, j) != 1:
            return False
    return True


def extendedEuclid(a, b):
    """return a tuple of three values: x, y and z, such that x is
    the GCD of a and b, and x = y * a + z * b"""
    if a == 0:
        return b, 0, 1
    else:
        g, y, x = extendedEuclid(b % a, a)
        return g, x - (b // a) * y, y


def modInv(a, m):
    """returns the multiplicative inverse of a in modulo m as a
       positive value between zero and m-1"""
    # notice that a and m need to co-prime to each other.
    if coPrime([a, m]):
        linearCombination = extendedEuclid(a, m)
        return linearCombination[1] % m
    else:
        return 0


def extractTwos(m):
    """m is a positive integer. A tuple (s, d) of integers is returned
    such that m = (2 ** s) * d."""
    # the problem can be break down to count how many '0's are there in
    # the end of bin(m). This can be done this way: m & a stretch of '1's
    # which can be represent as (2 ** n) - 1.
    assert m >= 0
    i = 0
    while m & (2 ** i) == 0:
        i += 1
    return i, m >> i


def int2baseTwo(x):
    """x is a positive integer. Convert it to base two as a list of integers
    in reverse order as a list."""
    # repeating x >>= 1 and x & 1 will do the trick
    assert x >= 0
    bitInverse = []
    while x != 0:
        bitInverse.append(x & 1)
        x >>= 1
    return bitInverse


def modExp(a, d, n):
    """returns a ** d (mod n)"""
    assert d >= 0
    assert n >= 0
    base2D = int2baseTwo(d)
    base2DLength = len(base2D)
    modArray = []
    result = 1
    for i in range(1, base2DLength + 1):
        if i == 1:
            modArray.append(a % n)
        else:
            modArray.append((modArray[i - 2] ** 2) % n)
    for i in range(0, base2DLength):
        if base2D[i] == 1:
            result *= base2D[i] * modArray[i]
    return result % n


def millerRabin(n, k):
    """
    Miller Rabin pseudo-prime test
    return True means likely a prime, (how sure about that, depending on k)
    return False means definitely a composite.
    Raise assertion error when n, k are not positive integers
    and n is not 1
    """
    assert n >= 1
    # ensure n is bigger than 1
    assert k > 0
    # ensure k is a positive integer so everything down here makes sense

    if n == 2:
        return True
    # make sure to return True if n == 2

    if n % 2 == 0:
        return False
    # immediately return False for all the even numbers bigger than 2

    extract2 = extractTwos(n - 1)
    s = extract2[0]
    d = extract2[1]
    assert 2 ** s * d == n - 1

    def tryComposite(a):
        """Inner function which will inspect whether a given witness
        will reveal the true identity of n. Will only be called within
        millerRabin"""
        x = modExp(a, d, n)
        if x == 1 or x == n - 1:
            return None
        else:
            for j in range(1, s):
                x = modExp(x, 2, n)
                if x == 1:
                    return False
                elif x == n - 1:
                    return None
            return False

    for i in range(0, k):
        a = random.randint(2, n - 2)
        if tryComposite(a) == False:
            return False
    return True  # actually, we should return probably true.


def primeSieve(k):
    """return a list with length k + 1, showing if list[i] == 1, i is a prime
    else if list[i] == 0, i is a composite, if list[i] == -1, not defined"""

    def isPrime(n):
        """return True is given number n is absolutely prime,
        return False is otherwise."""
        for i in range(2, int(n ** 0.5) + 1):
            if n % i == 0:
                return False
        return True

    result = [-1] * (k + 1)
    for i in range(2, int(k + 1)):
        if isPrime(i):
            result[i] = 1
        else:
            result[i] = 0
    return result


def findAPrime(a, b, k):
    """Return a pseudo prime number roughly between a and b,
    (could be larger than b). Raise ValueError if cannot find a
    pseudo prime after 10 * ln(x) + 3 tries. """


    x = random.randint(a, b)
    for i in range(0, int(10 * math.log(x) + 3)):
        if millerRabin(x, k):
            return x
        else:
            x += 1
    raise ValueError


def newKey(a, b, k):
    """ Try to find two large pseudo primes roughly between a and b.
    Generate public and private keys for RSA encryption.
    Raises ValueError if it fails to find one"""
    try:
        p = findAPrime(a, b, k)
        while True:
            q = findAPrime(a, b, k)
            if q != p:
                break
    except:
        raise ValueError

    n = p * q
    m = (p - 1) * (q - 1)

    e = 65537
    d = modInv(e, m)
    return (n, e, d, p, q)


def generate_key_pair():
    random.seed(get_random_number())
    n, e, d, p, q = newKey(2 ** 511, 2 ** 512, 50)
    public_key = str(n)+","+str(e)
    print("public key ",(n,e))
    py_public_key = {'modulus': n, 'publicExponent': e}
    public_key = decode(py_public_key, asn1Spec=RSAPublicKey())
    # Serialise SSH key data structure into DER stream
    der_serialisation = der_encoder(public_key)

    # Serialise DER stream into BASE64 stream
    b64_serialisation = '-----BEGIN RSA PUBLIC KEY-----\n'
    b64_serialisation += b64encode(der_serialisation).decode()
    b64_serialisation += '-----END RSA PUBLIC KEY-----\n'

    with open('rsa_public_key.pem', 'w') as key_file:
    	key_file.write(b64_serialisation)



    exp1 = d%(p-1) 
    exp2 = d % (q-1)
    coeff = modInv(p,q)
    py_private_key = {'modulus': n, 'publicExponent': e, 'privateExponent': d,  'prime1': p, 'prime2': q, 'exponent1': exp1, 'exponent2': exp2, 'coefficient': coeff}
    private_key = decode(py_private_key, asn1Spec=RSAPrivateKey())
    # Serialise SSH key data structure into DER stream
    der_serialisation_pk = der_encoder(private_key)

    # Serialise DER stream into BASE64 stream
    b64_serialisation = '-----BEGIN RSA PRIVATE KEY-----\n'
    b64_serialisation += b64encode(der_serialisation_pk).decode()
    b64_serialisation += '\n-----END RSA PRIVATE KEY-----\n'

    with open('rsa_private_key.pem', 'w') as key_file:
    	key_file.write(b64_serialisation)

