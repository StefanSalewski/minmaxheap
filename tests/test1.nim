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
assert h.empty

type
  O = object
    key: float

# we need < operator defines for elements
proc `<`(a, b: O): bool =
  a.key < b.key

var
  l = initMinMaxHeap[O]()
l.add(O(key: 1.2))
l.add(O(key: 0.9))
l.add(O(key: 3.3))
echo l.popMax # (key: 3.3)
echo l.popMin # (key: 0.9)
