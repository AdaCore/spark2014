package Nested is

   function Search return Integer
      with Post => (Search'Result >= 44);

end Nested;
