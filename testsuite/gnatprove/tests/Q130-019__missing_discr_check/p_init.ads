package P_Init with SPARK_Mode is

   type Enum is (One, Two);

   type T (E : Enum := One) is
      record
         X1 : Integer;
         case E is
            when One => null;
            when Two => X2 : Integer;
         end case;
      end record;

   subtype T_One is T (One);
   subtype T_Two is T (Two);

   function Init return T;

end P_Init;

