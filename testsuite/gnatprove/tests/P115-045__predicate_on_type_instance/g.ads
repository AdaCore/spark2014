-- Generic package G
generic
  type G_Formal_Type is private;
package G is
  X : G_Formal_Type; --@PREDICATE_CHECK_ON_DEFAULT_VALUE:FAIL
end;
