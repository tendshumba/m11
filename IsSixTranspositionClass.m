/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given a class D of involutions of a group G, and a positive integer m  +
+less than or equal to 6, determine if D is a class of 6-transpositions  +
+of G.                                                                   +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

IsMTranspositionClass := function(m, D, G)
  if m le 2 or m gt 6 then
    printf("The value of m must be between 3 and 6");
    return "fail";
  end if;
  assert Set(D[1]^G) eq Set(D);
  assert Order(D[1]) eq 2;
  D_set := Set(D);
  repeat  
    x := Random(D_set);
    y := (not IsEmpty(D_set diff {x})) select Random(D_set diff {x}) else x;
    if Order(x*y) gt m then
      return false;
    end if;
    D_set := D_set diff {x};
  until IsEmpty(D_set);
  return true;
end function;
 

IsMTranspositionGroup := function(m, D, G)
  if not sub<G | D> eq G then
    printf("The set of involutions do not generate G.\n");
    return false;
  end if;
  // split D into conjugacy classes
  D_indexed := IndexedSet(D);
  classes := [];
  repeat
    class := D_indexed[1]^G;
    Append(~classes, class);
    D_indexed := D_indexed diff class;
  until IsEmpty(D_indexed);
  // Check that each class is an m-transposition class
  for class in classes do
    if not IsMTranspositionClass(m, class, G) then
      return false;
    end if;
    break class;
  end for;
  if #classes eq 1 then
    return true;
  end if;
  for class in classes do
    class_diff := { y : y in classes | y ne class};
    if IsEmpty(class_diff) then
      return true;
    end if;
    for class_1 in class_diff do
      for x in class do
        for y in class_1 do
          if Order(x*y) gt m then
	    return false;
            break class;
	  end if;
        end for;
      end for;
    end for; 
  end for; 
  return true;
end function;

