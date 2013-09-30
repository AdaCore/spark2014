procedure Main2 is
--  TU: 2. The value of X'Loop_Entry [(loop_name)] is the value of X on entry
--  to the loop that is denoted by ``loop_name``. If the optional ``loop_name``
--  parameter is not provided, the closest enclosing loop is the default.
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
