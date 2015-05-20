procedure Main2 is
--  TU: 2. X'Loop_Entry [(loop_name)] denotes a constant object of the
--  type of X. [The value of this constant is the value of X on entry
--  to the loop that is denoted by ``loop_name`` or, if no
--  ``loop_name`` is provided, on entry to the closest enclosing
--  loop.]
   X : Integer := 0;
begin
   Outer:
      loop
         X := X + 1;
         Inner:
            loop
               X := X + 1;
               pragma Loop_Invariant (X'Loop_Entry = 0);
               --  Since loop_name was not provided, the
               --  Loop_Entry refers to Inner and hence
               --  the assertion will raise an exception
            end loop Inner;
         exit when X = 10;
      end loop Outer;
end Main2;
