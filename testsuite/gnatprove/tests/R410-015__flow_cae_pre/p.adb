package body P is
   X : Boolean := True;
   protected body PT is
      procedure Dummy with Pre => X;
      --  This is not "protected operation" in the Ada RM sense. It is meant to
      --  be called internally by genuine protected operations, e.g. from
      --  Visible below, but not from the outside. Here it is fine to access a
      --  global variable in the precondition.

      procedure Dummy is
      begin
         null;
      end;

      procedure Visible is
      begin
         Dummy;
      end;
   end;
end;
