package P is
   function F1 return Boolean is (True);
   function F2 return Boolean;
   function F3 return Boolean;
   function F4 return Boolean;
private
   function F2 return Boolean is (True);
end P;
