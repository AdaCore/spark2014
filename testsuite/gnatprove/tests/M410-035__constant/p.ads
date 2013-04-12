package P is
   C : constant Boolean;
   D : constant Boolean := True;
   E : constant Boolean;
   function F return Boolean;
   function K return Boolean;
   function H return Boolean is (K);
   function K return Boolean is (True);
   M : constant Boolean := H;
private
   C : constant Boolean := True;
   function G return Boolean is (F);
   function F return Boolean is (True);
   E : constant Boolean := G;
end P;
