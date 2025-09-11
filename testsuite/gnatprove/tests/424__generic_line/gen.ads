generic
  type T is range <>;
package Gen is

  procedure Incr (X : in out T)
    with Post => X = X'Old + 1;

end Gen;
