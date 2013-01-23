package Somebody is
   procedure P (X : in out Integer) with
     Post => X = X'Old / 2;
end Somebody;
