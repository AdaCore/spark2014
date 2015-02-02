package body Ghost_Illegal_2 is
   function Add (X, Y : Integer) return Integer is (X + Y);

   function Add_And_Double (X, Y : Integer) return Integer is
     --  TU: 12. A ghost entity shall only be referenced:
     --  * from within an assertion expression; or
     --  * from within an aspect specification [(i.e., either an
     --    ``aspect_specification`` or an aspect-specifying pragma)]; or
     --  * within the declaration or completion of a
     --    ghost entity (e.g., from within the body of a ghost subprogram); or
     --  * within a ghost statement; or
     --  * within a ``with_clause`` or ``use_clause``; or
     --  * within a renaming_declaration which either renames a ghost entity
     --    or occurs within a ghost subprogram or package.
   begin
      return Add (X, Y) * 2;
   end Add_And_Double;

   function Reads_A_Volatile return Integer is
     --  TU: 19. A ghost procedure shall not have an effectively
     --  volatile global input with the properties Async_Writers or
     --  Effective_Reads set to True. [This rule says, in effect,
     --  that ghost procedures are subject to the same restrictions as
     --  non-ghost functions with respect to reading volatile
     --  objects.] A name occurring within a ghost statement shall
     --  not denote an effectively volatile object with the properties
     --  Async_Writers or Effective_Reads set to True. [In other
     --  words, a ghost statement is subject to effectively the same
     --  restrictions as a ghost procedure.]
   begin
      return Vol_Int + 1;  --  Ghost functions are not allowed to read
                           --  Volatiles.
   end Reads_A_Volatile;


   function Is_Even (X : Integer) return Boolean is (X mod 2 = 0);

   procedure Ghost_Func_In_Flow_Exprpession (Par : in out Integer) is
      --  TU: 12. A ghost entity shall only be referenced:
      --  * from within an assertion expression; or
      --  * from within an aspect specification [(i.e., either an
      --    ``aspect_specification`` or an aspect-specifying pragma)]; or
      --  * within the declaration or completion of a
      --    ghost entity (e.g., from within the body of a ghost subprogram); or
      --  * within a ghost statement; or
      --  * within a ``with_clause`` or ``use_clause``; or
      --  * within a renaming_declaration which either renames a ghost entity
      --    or occurs within a ghost subprogram or package.
   begin
      if Is_Even (Par) then
         Par := 0;
      else
         Par := Par + 1;
      end if;
   end Ghost_Func_In_Flow_Exprpession;
end Ghost_Illegal_2;
