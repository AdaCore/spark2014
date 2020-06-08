procedure Main (X : Boolean; Y : out Boolean) with
  Global  => null,
  Depends => (Y => X),
  Post    => Y = X
is
   type T (D : Boolean) is record
      C : Boolean;
   end record;

   Q1 : constant T     := (D => X, C => X);
   Q2 : constant T (X) := (D => X, C => X);

   function F1 return Boolean is (Q1.D) with
     Global  => (Input => Q1, Proof_In => X),
     Depends => (F1'Result => Q1),
     Post    => F1'Result = X;

   function F2 return Boolean is (Q2.D) with
     Global  => (Input => (Q2, X)),
     Depends => (F2'Result => (Q2, X)),
     Post    => F2'Result = X;

begin
   Y := F1 and F2;
end Main;
