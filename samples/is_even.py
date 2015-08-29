#!/bin/env python3

def main(args):
    k = int(args[0])
    result = is_even(k)
    return result

def is_even(n):
    if n == 0:
        k = True
        return k
    else:
        result = is_odd(n - 1)
        return result

def is_odd(n):
    if n == 0:
        k = False
        return k
    else:
        result = is_even(n - 1)
        return result

if __name__ == '__main__':
    import sys
    print(main(sys.argv[1:]))
