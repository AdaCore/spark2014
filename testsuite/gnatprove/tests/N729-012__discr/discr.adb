procedure Discr with SPARK_Mode is
   type T is tagged null record;
   type U (D : Boolean) is new T with record
      case D is
         when True =>
            X : Integer;
         when False =>
            Y : Integer;
      end case;
   end record;

   function Get_X (V : U) return Integer is (V.X);
begin
   null;
end Discr;
