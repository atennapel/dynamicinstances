i = new E

f : () -> { i#op } i
f () =
  i#op;
  i



f : () -> <i:E> { i#op } i
f () =
  i = new E;
  i#op;
  i


