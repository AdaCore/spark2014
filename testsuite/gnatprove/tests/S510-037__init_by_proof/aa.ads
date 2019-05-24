package AA
   with SPARK_Mode
is
   Global_AA        : Natural ;

   procedure initGlobalsAA(status : out Natural)  with
     Global => (Output => Global_AA);

   procedure UseAA(X : in out Natural) with
     Global => (Input => Global_AA);
   --  Same as: "with Global => Global_Var;"

end AA;
