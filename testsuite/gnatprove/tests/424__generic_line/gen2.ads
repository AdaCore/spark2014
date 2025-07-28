with Gen;

generic
  type T is range <>;
package Gen2 is

  package G1 is new Gen (T);
  package G2 is new Gen (Integer);
  procedure My_Incr (X : in out T)
    with Post => X = X'Old + 1;

end Gen2;
