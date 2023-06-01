# Write Optimized Skip List Notes

[paper link](https://par.nsf.gov/servlets/purl/10027800)

## Pseudocode

```
Node:
  pivots: [(Value, Node)],
  buffer: [(Op, Value, Height)]
```

### Insert

#### Basic (Does not update pointers)
```
insert(root, value, height):
  insert(root.buffer, ins, value, height)
  if is_full(root):
    flush(root)

flush(node):
  let new_node = duplicate_without_buffer(node)
  for (TODO, value, height) in node.buffer:
    if node.height <= height:
      add_pivot(node, value)

    if node.height < height:
      split_node(node)

  if node.height > 1:
    for child in children:
      if is_full(child):
        flush(child)
  else node.height == 1:
    rebalance_leaves(node)

add_pivot(node, value):
  let (location, child) = find(node.pivots, value)
  insert(node.pivots, location, (value, child))
```

The complicating factor for Insert is that a node has multiple parents:
```
p0: [ | ... | ]  p1: [ | ... | ]
             \        /
         c: [ | ... | ]
```
for instance if some node `p` gets enough operations to flush and finds that it
needs to split into two nodes `p0` and `p1` but a child of `c` does not have
enough ops to flush, then both `p0` and `p1` will be parents of `c`. Further
operations can cause `p0` and `p1` to have an arbitrary number of flushes before
`c` gets updated. The one constraint that I _believe_ holds the run of pointers
to `c` will not be interrupted by a pointer to another child (proof: a pointer
to a child is only re-written when that child is updated, i.e. that child does a
Flush, if the child does a flush then all pointers to the child need to be
re-written). A single physical node can serve as multiple logical nodes, and the
Insert logic needs to handle this.

#### Physical to Logical Mapping

The skip list stores the logical search structure as a DAG of physical nodes.
While this is largely irrelevant to searches, during updates we need to reify
the physical structure to ensure that we update all the parents of a given
physical node, and that we don't flush to the same physical node multiple times.
There are a couple of ways to do this, most notable and additional indirection,
or a two-phase update.

##### Indirection

If we store a mapping table from logical to physical nodes we can reify the
mapping fairly easily, albeit at the expanse of an additional data structure.
```
Node:
  addr: LogicalAddr,
  pivots: [Key],
  children: [LogicalAddr],
  buffer: [(Key, Option<Value>, Height, Option<LogicalAddr>)],

insert(mapper, root_addr, key, value, height):
  let root = mapper.get_node(root_addr)
  root.buffer.insert(Ins, key, value, height, None)
  if is_full(root):
    root.flush(mapper)
    for node in mapper.updated() // †
      if node.is_full():
        node.flush()

flush(node, mapper):
  let new_node = Node.new()
  let ops = node.pivots.merge_join(node.buffer)
  new_node.apply(ops, mapper)
  mapper.set(logical_addr, new_node)

  if node.height == 1:
    rebalance_leaves(node)

apply(node, ops, mapper):
  for (key, value, height, logical_addr) in ops:
    var child_addr
    if node.height <= height: // and similar for existing pivots
      add_pivot(node, value)
      if new:
        child_addr = mapper.allocate_logical_addr()

    if height < node.height:
      let new_node = Node.new()
      apply(new_node, ops, mapper)
      mapper.set(logical_addr, new_node)

    node.add_to_child(key, value, height, child_addr)

add_pivot(node, value):
  let (location, child) = find(node.pivots, value)
  insert(node.pivots, location, (value, child))
```

Note the line marked with †. Despite having the physical-to-logical mapping
embedded within the DAG we still need a phase distinction to ensure that all ops
are added to a child atomically.

##### Two Phase

If we're already doing a two-phase update we may be able to do away with
persisting the mapper and just recover the info dynamically during a search
phase of the Insert. TODO

