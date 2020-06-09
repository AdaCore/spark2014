package Types is
   type My_Integer is new Integer with Default_Value => -12345;
   --  A scalar type with default initialization
   --  ??? Currently it needs to come from a withed unit because
   --  of a frontend bug T302-026, but it doesn't really matter.
end;
