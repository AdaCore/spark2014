package Count_Locations
  with SPARK_Mode
is
   pragma Warnings (GNATprove, Off, "function contract not available for proof",
                    Reason => "ignore info messages related to recursive ghost functions");

   subtype Sum_Type is Natural range 0 .. 100;
   subtype Index_Type is Positive range 1 .. 100;
   type Selected_Locations is array (Index_Type) of Boolean;
   type Max_Selected_Locations is array (Index_Type) of Positive;

   function Partial_Count_Selected_Locations (Sel : Selected_Locations; From : Index_Type) return Sum_Type is
      ((if Sel(From) then 1 else 0) + (if From < Index_Type'Last then Partial_Count_Selected_Locations (Sel, From + 1) else 0))
   with Ghost,
        Post => Partial_Count_Selected_Locations'Result <= Index_Type'Last - From + 1;
   pragma Annotate (GNATprove, Terminating, Partial_Count_Selected_Locations);

   function Count_Selected_Locations (Sel : Selected_Locations) return Sum_Type is
      (Partial_Count_Selected_Locations (Sel, Index_Type'First))
   with Ghost;

   function Check_Selected_Locations
     (Sel : Selected_Locations;
      Max : Max_Selected_Locations) return Boolean
   with Post =>
     Check_Selected_Locations'Result = (for all S in Index_Type => (if Sel(S) then Max(S) >= Count_Selected_Locations(Sel)));

end Count_Locations;
