package Basic is
   type Enum is (A, B, C);

   type R (X : Enum) is record
      Base : Integer;
      case X is
         when A =>
            A_Field : Integer;
         when B =>
            null;
         when C =>
            C_Field1 : Boolean;
            C_Field2 : Natural;
      end case;
   end record;

   type Enum_2 is (D, E, F);

   type Complex (X : Enum; Y : Enum_2; Z : Integer) is record
      Base : Integer;
      case X is
         when A =>
            A_Field : Integer;
         when B =>
            case Y is
               when D =>
                  D_Field : Enum;
               when E | F =>
                  E_F_Field : Enum_2;
            end case;
         when C =>
            C_Field1 : Boolean;
            C_Field2 : Natural;
            case Z is
               when 0 =>
                  Zero_Field : Integer;
               when 1 .. 10 =>
                  One_Ten_Field : Integer;
               when others =>
                  Others_Field : Natural;
            end case;
      end case;
   end record;

   procedure P (V : R);
end Basic;
