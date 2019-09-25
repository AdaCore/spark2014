package Parent.Child is
private
   function Maximum (X : Some_Type; Y : Some_Type) return Some_Type
   is (Some_Type'Max (X, Y));
end Parent.Child;
