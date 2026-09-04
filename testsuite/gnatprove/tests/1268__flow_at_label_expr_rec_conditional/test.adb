pragma Extensions_Allowed (All_Extensions);

procedure Test
  (Before_Choice, After_Choice : Boolean;
   Before_Left, After_Left     : Integer;
   Before_Right, After_Right   : Integer;
   Output_Left                 : out Integer;
   Output_Right                : out Integer)
with
  SPARK_Mode,
  Depends =>
    (Output_Left  => (Before_Choice, Before_Left, Before_Right),
     Output_Right => (Before_Choice, Before_Left, Before_Right),
     null         => (After_Choice, After_Left, After_Right))
is
   type Pair is record
      Left  : Integer;
      Right : Integer;
   end record;

   Choice : Boolean := Before_Choice;
   Left   : Pair := (Before_Left, Before_Right);
   Right  : Pair := (Before_Right, Before_Left);
   Saved  : Pair;

begin
   <<Capture>>
   Choice := After_Choice;
   Left := (After_Left, After_Right);
   Right := (After_Right, After_Left);
   Saved := Pair'((if Choice then Left else Right))'At (Capture);
   Output_Left := Saved.Left;
   Output_Right := Saved.Right;
end Test;
