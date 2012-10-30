--#inherit Parent_05.Private_Child_A_05, -- OK
--#        Parent_05.Public_Child_A_05;  -- error, public sibling
private package Parent_05.Private_Child_B_05
is
end Parent_05.Private_Child_B_05;
