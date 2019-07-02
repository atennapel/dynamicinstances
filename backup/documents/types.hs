f : forall t. () -> {i:Exception}<i> t
f () =
  i = new Exception;
  i#throw ()

g : forall t. () -> {i:Exception, j:Exception}<i, j> t
g () =
  f ();
  f ()

h : forall t. () -> {i*:Exception}<i*> t
h () =
  f ();
  h ()


% : forall t. (t -> Str) -> Str

printf : Str!{} => (Str)!{}
printf = handler {
  (%) f k -> \x -> k (f x)
}

with printf handle (%str ++ %int ++ %int)

x <- % str;
y <- % int

