procedure Incorrect_Logical_Equality_2 with SPARK_Mode is

   type Int_Option (Present : Boolean := False) is record
      case Present is
         when True => Content : Integer;
         when False => null;
      end case;
   end record;

   function Eq (X, Y : Int_Option) return Boolean is
     ((X.Present = Y.Present) and then
          (if X.Present then X.Content = Y.Content))
   with Annotate => (GNATprove, Logical_Equal);

   procedure Lemma_Int_Option_Eq (X, Y : Int_Option) with
     Ghost,
     Post => Eq (X, Y) =
       ((X.Present = Y.Present) and then
          (if X.Present then X.Content = Y.Content)),
     Annotate => (GNATprove, Automatic_Instantiation);

   procedure Lemma_Int_Option_Eq (X, Y : Int_Option) is
      C : constant Boolean := Eq (X, Y);
   begin
      pragma Assert
        (Eq (X, Y) =
         ((X.Present = Y.Present) and then
                (if X.Present then X.Content = Y.Content)));
   end Lemma_Int_Option_Eq;

begin
   null;
end Incorrect_Logical_Equality_2;
