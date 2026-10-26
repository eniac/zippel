"""Reading JSON produced next to PR code: bounded, strict, and typed at the boundary.

Every reader raises `Invalid` (a ValueError) on a bad shape, so callers parse
once and afterwards work only with values they can trust.
"""

import json
import math

MAX_JSON = 1024 * 1024


class Invalid(ValueError):
    """Data that does not have the shape its reader requires."""


def require(condition, message):
    if not condition:
        raise Invalid(message)


def load(data, limit=MAX_JSON):
    """JSON within a size limit, without duplicate keys or non-finite numbers."""
    require(len(data) <= limit, "JSON exceeds size limit")

    def strict_object(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, "duplicate JSON key")
            result[key] = value
        return result

    def nonfinite(value):
        raise Invalid(f"nonfinite JSON number: {value}")

    try:
        return json.loads(data, object_pairs_hook=strict_object, parse_constant=nonfinite)
    except (RecursionError, UnicodeError, json.JSONDecodeError) as error:
        raise Invalid("invalid JSON") from error


def dump(value):
    """Canonical JSON bytes: sorted keys and no whitespace."""
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def record(value, required, optional=frozenset(), extra=False):
    """An object with every `required` key and, unless `extra`, no keys besides
    `required` and `optional`."""
    require(type(value) is dict, "expected an object")
    keys = set(value)
    require(required <= keys, "missing fields")
    require(extra or keys <= required | optional, "unexpected fields")
    return value


def text(value, limit=256):
    require(isinstance(value, str) and len(value) <= limit, "expected a bounded string")
    return value


def machine_int(value):
    require(type(value) is int and 0 <= value < 2**64, "expected a nonnegative 64-bit integer")
    return value


def number(value):
    require(type(value) in (int, float) and math.isfinite(value) and 0 <= value < 1e15,
            "expected a nonnegative number")
    return value


def list_of(value, item, limit, length=None):
    """An array of at most `limit` (or exactly `length`) elements, each read by `item`."""
    require(isinstance(value, list) and len(value) <= limit and length in (None, len(value)),
            "expected a bounded array")
    return [item(element) for element in value]


def distinct(values):
    require(len(set(values)) == len(values), "expected distinct values")
    return values
