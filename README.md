# chika

This is a little programming language I'm working on, that's at about
the same abstraction level as C, but without a lot of the cruft.

My main goal with this project is *not* to make a better C, but rather
to learn about writing optimizing compilers, and compiling down to assembly.
I could do this by writing a C compiler, but I think it's easier to work with
a green-field language, without having to worry about the all the weird
decisions we're left with in C after all of these years.

# Examples

*This syntax is still experiemental*.

```chika
struct X {
  y: I32;
  z: I32;
}

fn foo(x: I32, y: I32): I32 {
  var s: X = {y: y, z: x};
  return s.y + s.z;
}

fn main() {
  print_int(foo(33, 34));
}
```