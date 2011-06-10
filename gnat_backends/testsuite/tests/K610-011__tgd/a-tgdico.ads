pragma Warnings (Off);
--  Turn of categorization warnings

generic
   type T (<>) is abstract tagged limited private;
   type Parameters (<>) is limited private;
   with function Constructor (Params : not null access Parameters) return T
     is abstract;

function Generic_Dispatching_Constructor
  (The_Tag : Integer;
   Params  : not null access Parameters) return T'Class;
pragma Preelaborate_05 (Generic_Dispatching_Constructor);
pragma Import (Intrinsic, Generic_Dispatching_Constructor);
