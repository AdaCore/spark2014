package Default_Init
  with SPARK_Mode
is
   type Result (Found : Boolean := False) is record
      case Found is
         when False => null;
         when True  => Content : Natural;
      end case;
   end record;

   R : Result;
end Default_Init;
