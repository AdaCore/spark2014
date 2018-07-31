package Q with SPARK_Mode => On is
   type T is private with Default_Initial_Condition => Initialized (T);
   function Initialized (Arg : T) return Boolean;
private
   pragma SPARK_Mode (Off);
   type T is record
      X : Integer := 0;
   end record;
   function Initialized (Arg : T) return Boolean is (Arg.X = 0);
end;
