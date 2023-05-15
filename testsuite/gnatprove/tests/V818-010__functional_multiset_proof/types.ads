package Types with SPARK_Mode => On is
   type Private_Type is private;

   function Eq (Left, Right : Private_Type) return Boolean with

     Post => Eq'Result = (Witness (Left) = Witness (Right));

   function Witness (X : Private_Type) return Integer with
     Ghost;

   --  Witness function used to express that Eq is an equivalence relation

private

   pragma SPARK_Mode (Off);

   type Private_Type is new Integer;

   function Eq (Left, Right : Private_Type) return Boolean is
     (Integer (Left) = Integer (Right));

   function Witness (X : Private_Type) return Integer is
     (Integer (X));

end Types;
