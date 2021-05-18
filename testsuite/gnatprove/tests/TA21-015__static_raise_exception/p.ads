package P is
   package Q is
      X : Integer := Integer (1 / (2 / 3));
   end Q;
   package R is
      Y : Integer := (if True then 1/0 else 1/0);
   end R;
end P;
