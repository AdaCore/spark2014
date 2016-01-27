package P is

   function Zero return Integer is (0);

   type Wrong is private with Default_Initial_Condition => Wrong.X / Zero = 0;

private
   type Wrong is record
      X : Integer := 0;
   end record;

end;
