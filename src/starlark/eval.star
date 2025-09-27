def _any(value, predicate):
    return any([eval(item, predicate) for item in value])

def _select(value, predicate):
    matches = eval(value, predicate)
    return value if matches else None

_functions = {
    "any": _any,
    "json": lambda value: json.decode(value),
    "in": lambda item, array: item in eval(item, array),
    "length": lambda value: len(value),
    "select": _select,
}

def eval(input, expr):
    if expr.type == "id":
        return input

    if expr.type in ["number", "string", "bool", "null"]:
        return expr.value

    if expr.type == "object":
        return {eval(input, key): eval(input, value)
            for (key, value) in expr.members}
    if expr.type == "array":
        return [eval(input, item) for item in expr.members]

    if expr.type == "not":
        return not eval(input, expr.rhs)
    if expr.type == "neg":
        return -eval(input, expr.rhs)
    if expr.type == "opt":
        return try_(lambda: eval(input, expr.lhs))

    if expr.type == "pipe":
        return eval(eval(input, expr.lhs), expr.rhs)
    if expr.type == "add":
        return eval(input, expr.lhs) + eval(input, expr.rhs)
    if expr.type == "sub":
        return eval(input, expr.lhs) - eval(input, expr.rhs)
    if expr.type == "mul":
        return eval(input, expr.lhs) * eval(input, expr.rhs)
    if expr.type == "div":
        return eval(input, expr.lhs) / eval(input, expr.rhs)
    if expr.type == "mod":
        return eval(input, expr.lhs) % eval(input, expr.rhs)
    if expr.type == "or":
        return eval(input, expr.lhs) or eval(input, expr.rhs)
    if expr.type == "and":
        return eval(input, expr.lhs) and eval(input, expr.rhs)
    if expr.type == "alt":
        left = eval(input, expr.lhs)
        return left if left not in [None, False] else eval(input, expr.rhs)
    if expr.type == "eq":
        return eval(input, expr.lhs) == eval(input, expr.rhs)
    if expr.type == "ne":
        return eval(input, expr.lhs) != eval(input, expr.rhs)
    if expr.type == "lt":
        return eval(input, expr.lhs) < eval(input, expr.rhs)
    if expr.type == "gt":
        return eval(input, expr.lhs) > eval(input, expr.rhs)
    if expr.type == "le":
        return eval(input, expr.lhs) <= eval(input, expr.rhs)
    if expr.type == "ge":
        return eval(input, expr.lhs) >= eval(input, expr.rhs)

    if expr.type == "index":
        (target, at) = expr.index
        target = eval(input, target)
        at = eval(input, at)
        return index(target, at)

    if expr.type == "slice":
        (target, start, end) = expr.slice
        target = eval(input, target)
        if target == None:
            return None
        if start and end:
            start = eval(input, start)
            end = eval(input, end)
            return target[start:end]
        if start:
            start = eval(input, start)
            return target[start:]
        if end:
            end = eval(input, end)
            return target[:end]
        return target

    if expr.type == "call":
        (name, args) = expr.call
        return _functions[name](input, *args)

    return None
