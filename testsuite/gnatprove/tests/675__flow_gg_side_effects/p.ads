package P is
   X : Boolean := False;
   function Set return Boolean with Side_Effects;
   procedure Proc1;
   procedure Proc2 (C : Boolean);
end;
