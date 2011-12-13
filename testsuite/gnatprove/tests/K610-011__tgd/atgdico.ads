pragma Warnings (Off);
--  Turn of categorization warnings

generic
   type T (<>) is abstract tagged limited private;
   type Parameters (<>) is limited private;
   with function Constructor (Params : not null access Parameters) return T
     is abstract;

procedure Atgdico
  (The_Tag : Integer;
   Params  : not null access Parameters);
