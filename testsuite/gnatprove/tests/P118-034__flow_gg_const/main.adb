with P;

procedure Main is

   Variable_Constant : constant Boolean := P.Read_Variable;
   Ordinary_Constant : constant Boolean := P.Simply_True;

   function Both_Are_True return Boolean with Pre => True;

   -------------------
   -- Both_Are_True --
   -------------------

   function Both_Are_True return Boolean is
     (Variable_Constant and Ordinary_Constant);

--  Start of processing for Main

begin
   pragma Assert (Both_Are_True);
end;
