# https://en.wikipedia.org/wiki/Min-max_heap
# http://www.akira.ruc.dk/~keld/teaching/algoritmedesign_f03/Artikler/02/Atkinson86.pdf
#
# This is basically a straight implementation following the original example code.
# Finally we used a container starting at index zero -- that makes calculating
# some indices a bit more expensive, but so we can use all Nim seq related procs
# without special precautions. To make the code more DRY some templates are
# used to replace pairs of min- and max- procs with only one. Original proc pairs
# remain for documentation purpose, but may bitrot eventually.

# (c) 2019 S. Salewski
# MIT license
# v 0.1
# 15-Mar-2019

##[
  The `minmaxheap` module implements a
  `heap data structure<https://en.wikipedia.org/wiki/Min-max_heap>`_
  that can be used as a
  `priority queue<https://en.wikipedia.org/wiki/Priority_queue>`_
  with fast O(log N) pop() operations for smallest and largest elements.

  Initial build is linear in number of elements, add() is O(log N)
  and read access for smallest and largest element is O(1).

  Basic usage
  -----------
  .. code-block:: Nim

    import minmaxheap

    var
      # h = toMinMaxHeap[int](@[5, 3, 9, 1, 0])
      h = toMinMaxHeap([5, 3, 9, 1, 0])

    echo $(h) # @[0, 5, 9, 1, 3]
    echo h.min # 0
    echo h.max # 9
    echo h.len # 5
    echo h.popMin # 0
    echo h.popMax # 9
    echo h.len # 3
    echo h.min # 1
    echo h.max # 5
    h.add(8)
    echo h.len # 4
    echo h.popMax # 8
    echo h.len # 3
    h.clear
    echo h.len # 0

  Usage with custom object
  ------------------------
  To use a `MinMaxHeap` with a custom object, the `<` operator must be
  implemented.

  .. code-block:: Nim

    type
      O = object
        key: float

    # we need < operator defined for elements
    proc `<`(a, b: O): bool =
      a.key < b.key

    var
      l = initMinMaxHeap[O]()
    l.add(O(key: 1.2))
    l.add(O(key: 0.9))
    l.add(O(key: 3.3))
    echo l.popMax # (key: 3.3)
    echo l.popMin # (key: 0.9)
]##

from bitops import fastlog2

type MinMaxHeap*[T] = distinct seq[T]

# NOTE: Nearly all used ints are naturals indeed, but typing Natural is a long word
# We may use Natural for some critical input parameters to avoid assert(i >= 0) tests

# borrow pragma does not work well for procs of this shape:

{.push inline.} # inline tiny procs

proc setLen[T](h: var MinMaxHeap[T]; i: int) =
  seq[T](h).setLen(i)

proc high[T](h: MinMaxHeap[T]): int =
  seq[T](h).high

proc `[]`[T](h: MinMaxHeap[T]; i: int): T =
  seq[T](h)[i]

proc `[]`[T](h: var MinMaxHeap[T]; i: int): var T =
  seq[T](h)[i]

proc `[]=`[T](h: var MinMaxHeap[T]; i: int; x: T) =
  seq[T](h)[i] = x

# following procs depend on start index of our seq -- initial original
# implenentation started with index 1, now we start with zero

const StartIndex = 0 # 1

#       0
#     /  \
#   1       2
#  /\    /\
# 3  4 5  6
# /\
# 7 8

# math for StartIndex = 1 commented out
proc firstChild(i: int): int =
  (i * 2) + 1 # i * 2

proc secondChild(i: int): int =
  (i + 1) * 2 # i * 2 + 1

proc hasGrandParent(h: MinMaxHeap; i: int): bool =
  i > 2 # i > 3

#proc parent(i: int): int =
template parent(i: int): int = # called often, so maybe better use a template instead inline proc
  # (i - 1) div 2 # i div 2
  (i - 1) shr 1 # avoid unused sign recovery

template grandparent(i: int): int =
  # (i - 3) div 4
  (i - 3) shr 2

proc hasChildren(h: MinMaxHeap; i: int): bool =
  # (i * 2) + 1 < h.len # i * 2 < h.len
  firstChild(i) < h.len

proc isMinLevel(i: int): bool =
  (fastLog2(i + 1) and 1) == 0 # (fastLog2(i) and 1) == 0

proc isGrandchild(h: MinMaxHeap; m, i: int): bool =
  #m > 2 * (i + 1) # m > 2 * i + 1
  m > secondChild(i)

{.pop.}

# Original procs, now unused, for documentation purpose only
# returns index, not value!
# all candidates have at least one child
proc smallestChildOrGrandchild(h: MinMaxHeap; i: int): int =
  assert hasChildren(h, i)
  var r: type(result)
  let l = h.len
  let c1 = i * 2
  let c2 = c1 + 1
  let g1 = c1 * 2
  let g2 = g1 + 1
  let g3 = g2 + 1
  let g4 = g3 + 1
  if g1 < l: # we have at least one grandchild
    r = g1
    if g2 < l and h[g2] < h[r]:
      r = g2
    if g3 < l: # second child has grandchild
      if h[g3] < h[r]:
        r = g3
      if g4 < l and h[g4] < h[r]:
        r = g4
    else:
      if c2 < l and h[c2] < h[r]:
        r = c2
    assert isGrandchild(h, r, i)
  else: # no grandchildreen
    r = c1
    if c2 < l and h[c2] < h[r]:
      r = c2
    assert not isGrandchild(h, r, i)
  return r

proc largestChildOrGrandchild(h: MinMaxHeap; i: int): int =
  assert hasChildren(h, i)
  var r: type(result)
  let l = h.len
  let c1 = i * 2
  let c2 = c1 + 1
  let g1 = c1 * 2
  let g2 = g1 + 1
  let g3 = g2 + 1
  let g4 = g3 + 1
  if g1 < l:
    r = g1
    if g2 < l and h[g2] > h[r]:
      r = g2
    if g3 < l:
      if h[g3] > h[r]:
        r = g3
      if g4 < l and h[g4] > h[r]:
        r = g4
    else:
      if c2 < l and h[c2] > h[r]:
        r = c2
    assert isGrandchild(h, r, i)
  else:
    r = c1
    if c2 < l and h[c2] > h[r]:
      r = c2
    assert not isGrandchild(h, r, i)
  return r

proc unusedChildOrGrandchild(h: MinMaxHeap; i: int; smallest: static[bool]): int =
  template tr(a: int) = # if index is valid and heap[index] is min/max, then store index
    if a < h.len:
      when smallest:
        if h[a] < h[result]:
          result = a
      else:
        if h[a] > h[result]:
           result = a
  assert hasChildren(h, i)
  let c1 = firstChild(i) # i * 2 + 1
  let c2 = c1 + 1 # second child
  let g1 = firstChild(c1) # c1 * 2 + 1
  let g2 = g1 + 1 # second grandchild
  let g3 = g2 + 1
  if g1 < h.len: # we have at least one grandchild
    result = g1
    g2.tr
    if g3 < h.len: # second child has grandchild # TODO nearly always true, so replace by true and always do c2.tr ?
      g3.tr
      tr(g3 + 1)
      assert isGrandchild(h, result, i)
    else:
      c2.tr
  else: # no grandchildreen
    result = c1
    c2.tr
    assert not isGrandchild(h, result, i)

proc childOrGrandchild(h: MinMaxHeap; i: int; smallest: static[bool]): int =
  template trx(a: int) = # if heap[index] is min/max, then store index
    when smallest:
      if h[a] < h[result]:
        result = a
    else:
      if h[a] > h[result]:
         result = a
  assert hasChildren(h, i)
  let c1 = firstChild(i) # i * 2 + 1
  let c2 = c1 + 1 # second child
  let g1 = firstChild(c1) # c1 * 2 + 1
  let g2 = g1 + 1 # second grandchild
  let g3 = g2 + 1
  let g4 = g3 + 1
  if g4 < h.len: # we have full 4 grandchilds
    result = g1
    g2.trx
    g3.trx
    g4.trx
    assert isGrandchild(h, result, i)
  elif not (g1 < h.len): # no grandchildreen
    result = c1
    if c2 < h.len:
      c2.trx
    assert not isGrandchild(h, result, i)
  else: # the rare case
    result = g1
    if g2 < h.len:
      g2.trx
    if g3 < h.len:
       g3.trx
    else:
       c2.trx

# again 4 unused original procs
proc pushDownMin(h: var MinMaxHeap; i: int) =
  if hasChildren(h, i):
    let m = childOrGrandchild(h, i, true)
    if isGrandchild(h, m, i):
      if h[m] < h[i]:
        swap(h[m], h[i])
        if h[m] > h[parent(m)]:
          swap(h[m], h[parent(m)])
        pushDownMin(h, m)
    elif h[m] < h[i]:
      swap(h[m], h[i])

proc pushDownMax(h: var MinMaxHeap; i: int) =
  if hasChildren(h, i):
    let m = childOrGrandchild(h, i, false)
    if isGrandchild(h, m, i):
      if h[m] > h[i]:
        swap(h[m], h[i])
        if h[m] < h[parent(m)]:
          swap(h[m], h[parent(m)])
        pushDownMax(h, m)
    elif h[m] > h[i]:
      swap(h[m], h[i])

proc pushDownMinIter(h: var MinMaxHeap; m: int) =
  var m = m
  while hasChildren(h, m):
    let i = m
    m = childOrGrandchild(h, i, smallest = true)
    if isGrandchild(h, m, i):
      if h[m] < h[i]:
        swap(h[m], h[i])
        if h[m] > h[parent(m)]:
          swap(h[m], h[parent(m)])
    elif h[m] < h[i]:
      swap(h[m], h[i])

proc pushDownMaxIter(h: var MinMaxHeap; m: int) =
  var m = m
  while hasChildren(h, m):
    let i = m
    m = childOrGrandchild(h, i, false)
    if isGrandchild(h, m, i):
      if h[m] > h[i]:
        swap(h[m], h[i])
        if h[m] < h[parent(m)]:
          swap(h[m], h[parent(m)])
    elif h[m] > h[i]:
      swap(h[m], h[i])

# the compressed template variant
proc pushDownIter(h: var MinMaxHeap; m: int; min: static[bool]) =
  template sw(a, b: int): bool = # test if swap is needed
    when min:
      h[a] < h[b]
    else:
      h[a] > h[b]
  var m = m
  while hasChildren(h, m):
    let i = m
    m = childOrGrandchild(h, i, min)
    if isGrandchild(h, m, i):
      if sw(m, i):
        swap(h[m], h[i])
        if sw(parent(m), m):
          swap(h[m], h[parent(m)])
    elif sw(m, i):
      swap(h[m], h[i])

proc pushDown(h: var MinMaxHeap; i: int) =
  if isMinLevel(i):
    #pushDownMin(h, i)
    pushDownIter(h, i, true)
  else:
    #pushDownMax(h, i)
    pushDownIter(h, i, false)

proc initMinMaxHeap*[T](): MinMaxHeap[T] =
  ## Create a new empty MinMaxHeap object.
  # a plain discard may be fine for Nim >= 0.19.4
  result = MinMaxHeap(newSeq[T]())

proc toMinMaxHeap*[T](h: openarray[T]): MinMaxHeap[T] =
  ## Create a new MinMaxHeap object initialized from an array or a seq.
  result = MinMaxHeap(@h)
  #for i in countdown((result.high - 1) div 2, 0):
  if result.high > 0: # caution, parent(0) may be undefined!
    for i in countdown(parent(result.high), 0):
    #for i in countdown(result.high div 2, 1):
      pushDown(result, i)

proc clear*[T](h: var MinMaxHeap[T]) =
  ## Remove all elements from `h`, making it empty.
  seq[T](h).setLen(0)

proc len*[T](h: MinMaxHeap[T]): int {.inline.} =
  ## Return the number of elements of `h`.
  seq[T](h).len

proc empty*[T](h: MinMaxHeap[T]): bool {.inline.} =
  ## Returns true if h.len == 0, false otherwise.
  seq[T](h).len == 0

# next two recursive procs are unused
proc pushUpMin(h: var MinMaxHeap; i: int) =
  if hasGrandParent(h, i) and h[i] < h[parent(parent(i))]:
    swap(h[i], h[parent(parent(i))])
    pushUpMin(h, parent(parent(i)))

proc pushUpMax(h: var MinMaxHeap; i: int) =
  if hasGrandParent(h, i) and h[i] > h[parent(parent(i))]:
    swap(h[i], h[parent(parent(i))])
    pushUpMax(h, parent(parent(i)))

proc pushUpMinIter(h: var MinMaxHeap; i: int) =
  var i = i
  while hasGrandParent(h, i) and h[i] < h[grandparent(i)]:
    swap(h[i], h[grandparent(i)])
    i = grandparent(i)

proc pushUpMaxIter(h: var MinMaxHeap; i: int) =
  var i = i
  while hasGrandParent(h, i) and h[i] > h[grandparent(i)]:
    swap(h[i], h[grandparent(i)])
    i = grandparent(i)

proc pushUp(h: var MinMaxHeap; i: int) =
  if i > StartIndex:
    if isMinLevel(i):
      if h[i] > h[parent(i)]:
        swap(h[i], h[parent(i)])
        # pushUpMax(h, parent(i))
        pushUpMaxIter(h, parent(i))
      else:
        # pushUpMin(h, i)
        pushUpMinIter(h, i)
    else:
      if h[i] < h[parent(i)]:
        swap(h[i], h[parent(i)])
        # pushUpMin(h, parent(i))
        pushUpMinIter(h, parent(i))
      else:
        # pushUpMax(h, i)
        pushUpMaxIter(h, i)

proc add*[T](h: var MinMaxHeap[T]; i: T) =
  ## Insert element `i` into `h`, maintaining order/invariants.
  system.add(seq[T](h), i)
  pushUp(h, h.high)

#proc removeMin[T](h: var MinMaxHeap[T]): T =
proc popMin*[T](h: var MinMaxHeap[T]): T =
  ## Delete and return smallest element from `h`, maintaining order/invariants.
  assert h.len > 0
  result = h[StartIndex]
  #h[StartIndex] = h.pop # pop is not borrowed
  h[StartIndex] = h[h.high]
  h.setLen(len(h) - 1)
  pushDown(h, StartIndex)

# this is for StartIndex = 0
#proc removeMax[T](h: var MinMaxHeap[T]): T =
proc popMax*[T](h: var MinMaxHeap[T]): T =
  ## Delete and return largest element from `h`, maintaining order/invariants.
  assert h.len > 0
  var i = high(h)
  if i > 1:
    i = 1 + (h[2] > h[1]).int
  result = h[i]
  h[i] = h[h.high]
  h.setLen(len(h) - 1)
  pushDown(h, i)

proc min*[T](h: var MinMaxHeap[T]): T {.inline.} =
  ## Return smallest element from `h`.
  assert h.len > 0
  result = h[StartIndex]

# this is for StartIndex = 0
proc max*[T](h: var MinMaxHeap[T]): T {.inline.} =
  ## Return largest element from `h`.
  assert h.len > 0
  var i = high(h)
  if i > 1:
    i = 1 + (h[2] > h[1]).int
  result = h[i]

proc `$`*[T](h: MinMaxHeap[T]): string =
  ## Turn `h` into its string representation.
  $(seq[T](h))

# Here starts testing stuff
when isMainModule:
  proc testRemoveMin[T](h: var MinMaxHeap[T]; n: int): int =
    while n > result and h.len > 0:
      let t = seq[T](h).min
      doassert(h.min == t)
      doassert(h.popMin == t)
      inc(result)

  proc testRemoveMax[T](h: var MinMaxHeap[T]; n: int): int =
    while n > result and h.len > 0:
      let t = seq[T](h).max
      doassert(h.max == t)
      doassert(h.popMax == t)
      inc(result)

  import random, algorithm
  proc test =
    const N = 1000
    var s = newSeq[int]()
    for i in 0 .. N - 1:
      assert(parent(parent(i + 3)) == grandparent(i + 3)) # grandparent is undefined for arg < 3
      s.add(rand(N))

    var h = toMinMaxHeap(s)
    s.sort
    while h.len > 0:
      assert h.popMax == s.pop
      assert h.popMin == s[0]
      s.delete(0)

  type
    OOO = object
      key: int

  proc `<`(o1, o2: OOO): bool =
    o1.key < o2.key

  block:
    test()
    let x = [0.5, 1, 2.2, 3, 4, 5, 6, 7, 8, 9]
    var s = toMinMaxHeap(x)
    echo "---\n", testRemoveMax(s, 3)
    s.add(2)
    echo "---\n", testRemoveMin(s, 3)
    s.add(99)
    echo "---\n", testRemoveMax(s, 3)
    s.add(-5)
    echo "---\n", testRemoveMin(s, 3)

  block:
    var x = newSeq[OOO]()
    x.add(OOO(key: 0))
    x.add(OOO(key: 7))
    x.add(OOO(key: 5))
    x.add(OOO(key: 13))
    x.add(OOO(key: 1))
    x.add(OOO(key: 7))
    x.add(OOO(key: 3))
    var s = toMinMaxHeap(x)
    echo "---\n", testRemoveMax(s, 3)
    s.add(OOO(key: 13))
    s.add(OOO(key: 7))
    assert s.popMax.key == 13

