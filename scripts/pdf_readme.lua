-- Adapt GitHub presentation to a printable document.
local repository = 'https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis'

local function remote(target)
  return target:match('^https?://') ~= nil
end

local function flatten_table(t)
  local blocks = pandoc.List()
  local function rows(rs)
    for _, row in ipairs(rs) do
      for _, cell in ipairs(row.cells) do blocks:extend(cell.contents) end
    end
  end
  rows(t.head.rows)
  for _, body in ipairs(t.bodies) do rows(body.head); rows(body.body) end
  rows(t.foot.rows)
  return blocks
end

function Pandoc(doc)
  doc = doc:walk {
    RawBlock = function(raw)
      if raw.format ~= 'html' then return nil end
      local html = pandoc.read(raw.text, 'html')
      -- The README's HTML tables are figure galleries, not data tables.
      return html:walk {Table = flatten_table}.blocks
    end,
    RawInline = function(raw)
      if raw.format == 'html' then return {} end
    end
  }
  doc = doc:walk {
    Link = function(link)
      if not link.target:match('^[%a][%w+.-]*:') and not link.target:match('^#') then
        link.target = repository .. '/blob/main/' .. link.target:gsub('^%./', '')
      end
      return link
    end
  }
  return doc:walk {
    Table = function(t)
      -- GFM gives tables unspecified widths, which LaTeX renders as unwrapped columns.
      local n = #t.colspecs
      for i, spec in ipairs(t.colspecs) do
        spec[2] = n == 2 and (i == 1 and 0.36 or 0.64) or 1 / n
      end
      return t
    end,
    Code = function(code)
      local latex = pandoc.write(pandoc.Pandoc({pandoc.Plain({code})}), 'latex')
      return pandoc.RawInline('latex', latex:gsub('\\_', '\\_\\allowbreak{}'))
    end,
    Image = function(img)
      -- Remote badges are presentation-only; omit them from the deterministic PDF.
      if remote(img.src) then return pandoc.Span(img.caption) end
      img.attributes.width = '95%'
      img.attributes.height = nil
      return img
    end
  }
end
