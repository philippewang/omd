(***********************************************************************)
(* omd: Markdown frontend in OCaml                                     *)
(* (c) 2013 by Philippe Wang <philippe.wang@cl.cam.ac.uk>              *)
(* Licence : CeCILL-B                                                  *)
(* http://www.cecill.info/licences/Licence_CeCILL-B_V1-en.html         *)
(***********************************************************************)

type md_element = 
  | Paragraph of md
  | Text of string
  | Emph of md
  | Bold of md
  | Ul of li list
  | Ol of li list
  | Code of string (* html entities are to be converted *later* *)
  | Br
  | Hr
  | Url of href * string * title
  | Html of string
  | H1 of md
  | H2 of md
  | H3 of md
  | H4 of md
  | H5 of md
  | H6 of md
  | NL
and href = string
and title = string
and li = Li of md
and md = md_element list

let htmlentities s =
  let b = Buffer.create 42 in
    for i = 0 to String.length s - 1 do
      match s.[i] with
        | ( '0' .. '9' | 'a' .. 'z' | 'A' .. 'Z' ) as c -> Buffer.add_char b c
        | '"' -> Buffer.add_string b "&quot;"
        | '\'' -> Buffer.add_string b "&apos;"
        | '&' -> Buffer.add_string b "&amp;"
        | '<' -> Buffer.add_string b "&lt;"
        | '>' -> Buffer.add_string b "&gt;"
        | '\\' -> Buffer.add_string b "&#92;"
        | c -> Buffer.add_char b c
    done;
    Buffer.contents b

(* let html_of_md md = *)
(*   let b = Buffer.create 42 in *)
(*   let rec loop = function *)
(*     | Paragraph md -> *)
(*         Buffer.add_string b "<p>"; *)
(*         List.iter loop md; *)
(*         Buffer.add_string b "</p>" *)
(*     | Text t -> *)
(*         Buffer.add_string b t *)
(*     | Emph md -> *)
(*         Buffer.add_string b "<em>"; *)
(*         List.iter loop md; *)
(*         Buffer.add_string b "</em>" *)
(*     | Bold md -> *)
(*         Buffer.add_string b "<strong>"; *)
(*         List.iter loop md; *)
(*         Buffer.add_string b "</strong>" *)
(*     | Ul l -> *)
(*         Buffer.add_string b "<ul>"; *)
(*         List.iter *)
(*           (fun (Li li) -> *)
(*             Buffer.add_string b "<li>"; *)
(*             List.iter loop li; *)
(*             Buffer.add_string b "</li>") *)
(*           l; *)
(*         Buffer.add_string b "</ul>" *)
(*     | Ol l -> *)
(*         Buffer.add_string b "<ol>"; *)
(*         List.iter *)
(*           (fun (Li li) -> *)
(*             Buffer.add_string b "<li>"; *)
(*             List.iter loop li; *)
(*             Buffer.add_string b "</li>") *)
(*           l; *)
(*         Buffer.add_string b "</ol>" *)
(*     | Code c -> *)
(*         Buffer.add_string b "<pre>"; *)
(*         Buffer.add_string b (htmlentities c); *)
(*         Buffer.add_string b "</pre>" *)
(*     | Br -> *)
(*         Buffer.add_string b "<br/>" *)
(*     | Hr -> *)
(*         Buffer.add_string b "<hr/>" *)
(*     | Html s -> *)
(*         Buffer.add_string b s *)
(*     | Url (href,s,title) -> *)
(*         let s = htmlentities s in *)
(*           Buffer.add_string b "<a href='"; *)
(*           Buffer.add_string b (htmlentities href); *)
(*           Buffer.add_string b "'"; *)
(*           if title <> "" then *)
(*             begin *)
(*               Buffer.add_string b " title='"; *)
(*               Buffer.add_string b (htmlentities title); *)
(*               Buffer.add_string b "'"; *)
(*             end; *)
(*           Buffer.add_string b ">"; *)
(*           Buffer.add_string b s; *)
(*           Buffer.add_string b "</a>"; *)
(*     | H1 md -> *)
(*         Buffer.add_string b "<h1>"; *)
(*         List.iter loop md; *)
(*         Buffer.add_string b "</h1>" *)
(*     | H2 md -> *)
(*         Buffer.add_string b "<h2>"; *)
(*         List.iter loop md; *)
(*         Buffer.add_string b "</h2>" *)
(*     | H3 md -> *)
(*         Buffer.add_string b "<h3>"; *)
(*         List.iter loop md; *)
(*         Buffer.add_string b "</h3>" *)
(*     | H4 md -> *)
(*         Buffer.add_string b "<h4>"; *)
(*         List.iter loop md; *)
(*         Buffer.add_string b "</h4>" *)
(*     | H5 md -> *)
(*         Buffer.add_string b "<h5>"; *)
(*         List.iter loop md; *)
(*         Buffer.add_string b "</h5>" *)
(*     | H6 md -> *)
(*         Buffer.add_string b "<h6>"; *)
(*         List.iter loop md; *)
(*         Buffer.add_string b "</h6>" *)
(*     | NL -> *)
(*         Buffer.add_char b '\n' *)
(*   in *)
(*     List.iter loop md; *)
(*     Buffer.contents b *)

let make_paragraphs md =
  let rec remove_prefix prefix = function
    | [] ->
        []
    | e::tl as l ->
        if e = prefix then
          remove_prefix prefix tl
        else
          l
  in
  let rec loop cp accu = function (* cp means current paragraph *)
    | [] ->
        let accu =
          if cp = [] || cp = [NL] then
            accu
          else
            Paragraph(List.rev cp)::accu
        in
          List.rev accu
    | (Code _ | H1 _ | H2 _ | H3 _ | H4 _ | H5 _ | H6 _ | Html _ | Br | Hr) as e :: tl->
        if cp = [] || cp = [NL] then 
          loop cp (e::accu) tl
        else
          loop [] (e::Paragraph(List.rev cp)::accu) tl
    | Text "\n" :: _ | Paragraph _ :: _ ->
        assert false
    | NL::NL::tl ->
        let tl = remove_prefix NL tl in
          begin match cp with
            | [] | [NL] ->
                loop [] (NL::accu) tl
            | _ ->
                loop [] (Paragraph(List.rev cp)::accu) tl
          end
    | x::tl ->
        loop (x::cp) accu tl
  in
    loop [] [] md

(* let make_paragraphs x = x  *)


let rec html_of_md md = 
  let empty s =
    let rec loop i =
      if i < String.length s then
        match s.[i] with
          | ' ' | '\n' -> loop (i+1)
          | _ -> false
      else
        true
    in
      loop 0
  in    
  let b = Buffer.create 42 in
  let rec loop indent = function
    | Paragraph md :: tl ->
        (let s = html_of_md md in
           if empty s then
             ()
           else
             begin
               Buffer.add_string b "<p>";
               Buffer.add_string b s;
               Buffer.add_string b "</p>\n";
             end);
        loop indent tl
    | Text t :: tl ->
        Buffer.add_string b t;
        (* Buffer.add_string b (htmlentities t); *)
        loop indent tl
    | Emph md :: tl ->
        Buffer.add_string b "<em>";
        loop indent md;
        Buffer.add_string b "</em>";
        loop indent tl
    | Bold md :: tl ->
        Buffer.add_string b "<strong>";
        loop indent md;
        Buffer.add_string b "</strong>";
        loop indent tl
    | Ul [Li((Ul(_)::_) as l)] :: tl ->
        loop indent l;
        loop indent tl
    | Ul l :: tl ->
        Buffer.add_string b "\n";
        for i = 0 to indent do Buffer.add_char b ' ' done;
        Buffer.add_string b "<ul>\n";
        List.iter
          (fun (Li li) ->
            for i = 0 to indent + 1 do Buffer.add_char b ' ' done;
            Buffer.add_string b "<li>";
            loop (indent+2) li;
            Buffer.add_string b "\n";
            for i = 0 to indent + 1 do Buffer.add_char b ' ' done;
            Buffer.add_string b "</li>\n")
          l;
        for i = 0 to indent do Buffer.add_char b ' ' done;
        Buffer.add_string b "</ul>\n";
        loop indent tl
    | Ol l :: tl ->
        Buffer.add_string b "<ol>";
        List.iter
          (fun (Li li) ->
            Buffer.add_string b "<li>";
            loop indent li;
            Buffer.add_string b "</li>")
          l;
        Buffer.add_string b "</ol>\n";
        loop indent tl
    | Code c :: tl ->
        Buffer.add_string b "<pre>";
        Buffer.add_string b (htmlentities c);
        Buffer.add_string b "</pre>\n";
        loop indent tl
    | Br :: tl ->
        Buffer.add_string b "<br/>\n";
        loop indent tl
    | Hr :: tl ->
        Buffer.add_string b "<hr/>\n";
        loop indent tl
    | Html s :: tl ->
        Buffer.add_string b s;
        loop indent tl
    | Url (href,s,title) :: tl ->
        let s = htmlentities s in
          Buffer.add_string b "<a href='";
          Buffer.add_string b (htmlentities href);
          Buffer.add_string b "'";
          if title <> "" then 
            begin
              Buffer.add_string b " title='";
              Buffer.add_string b (htmlentities title);
              Buffer.add_string b "'";
            end;
          Buffer.add_string b ">";
          Buffer.add_string b s;
          Buffer.add_string b "</a>";
          loop indent tl
    | H1 md :: tl ->
        Buffer.add_string b "<h1>";
        loop indent md;
        Buffer.add_string b "</h1>";
        loop indent tl
    | H2 md :: tl ->
        Buffer.add_string b "<h2>";
        loop indent md;
        Buffer.add_string b "</h2>";
        loop indent tl
    | H3 md :: tl ->
        Buffer.add_string b "<h3>";
        loop indent md;
        Buffer.add_string b "</h3>";
        loop indent tl
    | H4 md :: tl ->
        Buffer.add_string b "<h4>";
        loop indent md;
        Buffer.add_string b "</h4>";
        loop indent tl
    | H5 md :: tl ->
        Buffer.add_string b "<h5>";
        loop indent md;
        Buffer.add_string b "</h5>";
        loop indent tl
    | H6 md :: tl ->
        Buffer.add_string b "<h6>";
        loop indent md;
        Buffer.add_string b "</h6>";
        loop indent tl
    | NL :: tl ->
        Buffer.add_char b '\n';
        loop indent tl
    | [] -> ()
  in 
    loop 0 md;
    Buffer.contents b

