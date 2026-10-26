package Imported is
   procedure Check (X : Integer; Y : out Integer)
   with Pre => X >= 0 and then X < Integer'Last;
end Imported;
