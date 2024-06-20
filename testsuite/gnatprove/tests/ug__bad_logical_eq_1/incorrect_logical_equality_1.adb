procedure Incorrect_Logical_Equality_1 with SPARK_Mode is

   type Int_Option (Present : Boolean := False) is record
      case Present is
         when True => Content : Integer;
         when False => null;
      end case;
   end record;

   function Eq (X, Y : Int_Option) return Boolean with
     Import,
     Global => null,
     Annotate => (GNATprove, Logical_Equal);

   procedure Lemma_Int_Option_Eq (X, Y : Int_Option) with
     Import,
     Ghost,
     Global => null,
     Post => Eq (X, Y) =
       ((X.Present = Y.Present) and then
          (if X.Present then X.Content = Y.Content)),
       Annotate => (GNATprove, Automatic_Instantiation);

   procedure Test with Global => null is
      V : Int_Option := (Present => False);
      C : constant Boolean := Eq (V, V);
   begin
      pragma Assert (False);
   end Test;

begin
   null;
end Incorrect_Logical_Equality_1;
