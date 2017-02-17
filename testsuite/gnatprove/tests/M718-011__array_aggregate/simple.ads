with Types;       use Types;

package Simple is



   function Foo (Init_Val : Integer) return Array_1D
   with Post => (Foo'Result = Array_1D'(1 => 10, others => Init_Val + 1));

end Simple;
