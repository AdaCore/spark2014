package New_Duration is
   type ND is private;
   function Convert (X : ND) return Duration;
private
   type ND is new Duration;
   function Convert (X : ND) return Duration is (Duration (X));
end;
