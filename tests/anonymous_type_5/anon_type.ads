package Anon_Type is
   type Tab is array(Integer  range <>)
   of Integer range 0 .. 10;
   procedure To_Fix (Y : out Integer);
end Anon_Type;

