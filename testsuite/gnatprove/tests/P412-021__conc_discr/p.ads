package P is

   protected type PT (X : Integer) is
   end;

   task type TT (X : Integer);

   PO : PT (0);
   TO : TT (0);

   PO_X : constant Integer := PO.X with Ghost;
   TO_X : constant Integer := TO.X with Ghost;

   pragma Assert (PO_X = 0);
   pragma Assert (TO_X = 0);

end;
