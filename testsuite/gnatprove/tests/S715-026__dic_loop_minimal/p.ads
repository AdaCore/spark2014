package P is
   type T is private with Default_Initial_Condition =>
      (for all J in 1 .. 3 => J > 0 and Trivial (T));
   --  There will be two entities whose scope is the internally generated DIC
   --  procedure: the implicit formal parameter "_object" and the quantified
   --  expression parameter "J".

   function Trivial (Arg : T) return Boolean is (True);
private
   type T is null record;
end;
