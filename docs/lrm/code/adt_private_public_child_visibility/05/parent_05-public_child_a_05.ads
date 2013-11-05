--#inherit Parent_05,                     -- OK
--#        Parent_05.Private_Child_A_05;  -- error, private sibling
package Parent_05.Public_Child_A_05
is
  function G (X : Integer) return Integer;
end Parent_05.Public_Child_A_05;
