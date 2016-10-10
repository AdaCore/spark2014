package Test with SPARK_Mode is

   subtype T is Positive range 5 .. 16;

   procedure Do_Smth (I : Boolean; Oha : out T)
   with
      Global => null,
      Depends => (Oha => I);

end Test;

