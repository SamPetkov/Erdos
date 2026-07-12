-- Prepare the Markdown manuscript for a standalone paper-style LaTeX build.
-- The Markdown title and status block are supplied as Pandoc metadata, while
-- the remaining heading hierarchy is promoted by one level.

local in_front_matter = true
local saw_title = false

function Header(element)
  if not saw_title and element.level == 1 then
    saw_title = true
    return {}
  end

  local title = pandoc.utils.stringify(element.content)
  local is_abstract = title == "Abstract"
  if is_abstract then
    in_front_matter = false
    element.classes:insert("unnumbered")
  end

  if element.level > 1 then
    element.level = element.level - 1
  end

  if is_abstract then
    return {
      pandoc.RawBlock("latex", "\\clearpage"),
      element,
    }
  end
  return element
end

function Para(element)
  if in_front_matter and saw_title then
    return {}
  end
  return element
end

function Code(element)
  -- Long inline notation is represented as code in the canonical Markdown.
  -- Add invisible TeX break opportunities at natural separators so those
  -- spans do not force overfull lines or globally loose paragraph spacing.
  if #element.text < 18 then
    return element
  end

  local break_after = {
    ["_"] = true,
    ["/"] = true,
    ["="] = true,
    ["<"] = true,
    [">"] = true,
    ["+"] = true,
    [","] = true,
    [";"] = true,
    [")"] = true,
    ["]"] = true,
  }
  local result = {}
  local chunk = ""

  for index = 1, #element.text do
    local character = element.text:sub(index, index)
    chunk = chunk .. character
    if break_after[character] and index < #element.text then
      table.insert(result, pandoc.Code(chunk))
      table.insert(result, pandoc.RawInline("latex", "\\allowbreak{}"))
      chunk = ""
    end
  end

  if chunk ~= "" then
    table.insert(result, pandoc.Code(chunk))
  end
  return result
end

function Math(element)
  if element.mathtype == "DisplayMath" then
    -- Amsmath requires equation tags outside a nested split environment.
    -- The Markdown renderer accepts the source form, so normalize it only in
    -- the generated publication artifact and leave the canonical proof intact.
    element.text = element.text:gsub(
      "(\\tag%b{})%s*(\\end{split})",
      "%2\n%1"
    )

    -- The notation line (7.12) is wider than an A4 text block.  Break it at
    -- its existing source newline, without changing any mathematical text.
    if element.text:find("\\tag{7.12}", 1, true) then
      local body = element.text:gsub("%s*\\tag{7%.12}%s*", "")
      body = body:gsub("^%s+", ""):gsub("%s+$", "")
      body = body:gsub("\n%s*z_i=", "\\\\\nz_i=", 1)
      element.text = "\\begin{gathered}\n"
        .. body
        .. "\n\\end{gathered}\n\\tag{7.12}"
    end
  end
  return element
end
