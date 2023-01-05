package Types with SPARK_Mode is

   type My_Int is new Integer with Relaxed_Initialization;

   type T (B : Boolean) is record
      case B is
         when True =>
            X : My_Int;
         when False =>
            Y : Integer;
      end case;
   end record;

   procedure Write_Part (X : out T; C : Boolean) with
     Global => null;

end Types;
