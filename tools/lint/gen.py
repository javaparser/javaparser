import json
from pprint import pprint

with open("src/sarif-schema-2.1.0.json") as fh:
    schema = json.load(fh)

visited_defs = set()

def enqueue(ref):
    if ref not in visited_defs:
        queue_classes.append((ref, schema['definitions'][ref]))
        visited_defs.add(ref)


def type(prop):
    t = prop.get('type', None)
    if t == 'string':
        return 'String'
    if t == 'integer':
        return 'Int'
    if t == ['string', 'null']:
        return 'String?'
    if t == 'array' or (t and 'array' in t):
        t = prop['items'].get('$ref', None)
        if t:
            t = t[14:]
            enqueue(t)
        else:
            t = prop['items'].get('type', t)

        return f"MutableList<{t}>"

    ref = prop.get('$ref', None)
    if ref:
        ref = ref[14:]
        enqueue(ref)
        return ref

    return "type unsupported"


#        prefix = '?' if 'null' in t else ''


def get_props(obj):
    s = []
    for (k, v) in obj['properties'].items():
        if k.startswith('$'): continue
        s.append(f"/** {v['description']} */ \n var {k} : {type(v)}")
    return ',\n'.join(s)


queue_classes = [("Sarif", schema)]


def make_class(name, obj):
    print(f"""
    /** 
     * {obj['description']}
     */
    data class {name}({get_props(obj)})
    """)


while queue_classes:
    (name, c) = queue_classes.pop()
    make_class(name, c)
