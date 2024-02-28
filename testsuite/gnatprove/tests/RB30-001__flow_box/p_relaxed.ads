package P_Relaxed is

   type T (Valid : Boolean) is record
      case Valid is
         when True =>
            C : Integer;
         when False =>
            null;
      end case;
   end record with Relaxed_Initialization;

   procedure Get (X : Integer; Y : out T) with Pre => not Y'Constrained;

end;
