local Core = {}
Core.VERSION = "1.4.7"

local INDEX_BASE = 4194304

local function isFiniteNumber(value)
    return type(value) == "number"
        and value == value
        and value ~= math.huge
        and value ~= -math.huge
end

local function addWarning(ctx, lineNo, message)
    ctx.warningCount = ctx.warningCount + 1
    if #ctx.warnings < 30 then
        ctx.warnings[#ctx.warnings + 1] = string.format("第 %d 行: %s", lineNo, message)
    end
end

local function parseFaceIndex(token, vertexCount)
    local slash = string.find(token, "/", 1, true)
    local head = slash and string.sub(token, 1, slash - 1) or token
    if head == "" then
        return nil, "空索引"
    end
    local index = tonumber(head)
    if not isFiniteNumber(index) or index % 1 ~= 0 then
        return nil, "索引不是整数"
    end
    if index == 0 then
        return nil, "索引不能为 0"
    end
    if index < 0 then
        index = vertexCount + index + 1
    end
    if index < 1 then
        return nil, "负索引越界"
    end
    if index > vertexCount then
        return nil, "索引越界"
    end
    return index
end

local function triangulatePolygon(vertices, polygon)
    local count = #polygon
    if count < 4 then
        return {}
    end
    if count > 512 then
        return nil, "多边形顶点超过 512，跳过三角化"
    end

    local nx, ny, nz = 0, 0, 0
    for i = 1, count do
        local a = polygon[i] * 3
        local b = polygon[i % count + 1] * 3
        local ax, ay, az = vertices[a - 2], vertices[a - 1], vertices[a]
        local bx, by, bz = vertices[b - 2], vertices[b - 1], vertices[b]
        nx = nx + (ay - by) * (az + bz)
        ny = ny + (az - bz) * (ax + bx)
        nz = nz + (ax - bx) * (ay + by)
    end
    if math.abs(nx) + math.abs(ny) + math.abs(nz) < 1e-12 then
        return nil, "面法线退化"
    end

    local axis
    if math.abs(nx) >= math.abs(ny) and math.abs(nx) >= math.abs(nz) then
        axis = 1
    elseif math.abs(ny) >= math.abs(nz) then
        axis = 2
    else
        axis = 3
    end

    local rawX, rawY = {}, {}
    local minX, minY = math.huge, math.huge
    local maxX, maxY = -math.huge, -math.huge
    for i = 1, count do
        local base = polygon[i] * 3
        local x, y, z = vertices[base - 2], vertices[base - 1], vertices[base]
        local u, v
        if axis == 1 then
            u, v = y, z
        elseif axis == 2 then
            u, v = x, z
        else
            u, v = x, y
        end
        rawX[i], rawY[i] = u, v
        if u < minX then minX = u end
        if v < minY then minY = v end
        if u > maxX then maxX = u end
        if v > maxY then maxY = v end
    end

    local projectedX, projectedY = {}, {}
    for i = 1, count do
        projectedX[i] = rawX[i] - minX
        projectedY[i] = rawY[i] - minY
    end

    local projectionScale = math.max(maxX - minX, maxY - minY, 1e-9)
    local eps = projectionScale * projectionScale * 1e-10

    local area = 0
    for i = 1, count do
        local j = i % count + 1
        area = area + projectedX[i] * projectedY[j] - projectedX[j] * projectedY[i]
    end
    area = area * 0.5
    if math.abs(area) < eps then
        return nil, "投影面积退化"
    end

    if area < 0 then
        local reversedX, reversedY, reversedPolygon = {}, {}, {}
        for i = 1, count do
            local source = count - i + 1
            reversedX[i] = projectedX[source]
            reversedY[i] = projectedY[source]
            reversedPolygon[i] = polygon[source]
        end
        projectedX, projectedY, polygon = reversedX, reversedY, reversedPolygon
    end

    local function cross2(ax, ay, bx, by, cx, cy)
        return (bx - ax) * (cy - ay) - (by - ay) * (cx - ax)
    end

    local function isConvex(a, b, c)
        return cross2(projectedX[a], projectedY[a], projectedX[b], projectedY[b], projectedX[c], projectedY[c]) > eps
    end

    local function pointInTriangle(a, b, c, p)
        local d1 = cross2(projectedX[a], projectedY[a], projectedX[b], projectedY[b], projectedX[p], projectedY[p])
        local d2 = cross2(projectedX[b], projectedY[b], projectedX[c], projectedY[c], projectedX[p], projectedY[p])
        local d3 = cross2(projectedX[c], projectedY[c], projectedX[a], projectedY[a], projectedX[p], projectedY[p])
        local hasNegative = d1 < -eps or d2 < -eps or d3 < -eps
        local hasPositive = d1 > eps or d2 > eps or d3 > eps
        return not (hasNegative and hasPositive)
    end

    local indices = {}
    for i = 1, count do
        indices[i] = i
    end

    local diagonals = {}
    local guard = 0
    while #indices > 3 do
        local clipped = false
        local remaining = #indices
        for k = 1, remaining do
            local previous = indices[(k - 2) % remaining + 1]
            local current = indices[k]
            local nextIndex = indices[k % remaining + 1]
            if isConvex(previous, current, nextIndex) then
                local contains = false
                for j = 1, remaining do
                    local p = indices[j]
                    if p ~= previous and p ~= current and p ~= nextIndex then
                        if pointInTriangle(previous, current, nextIndex, p) then
                            contains = true
                            break
                        end
                    end
                end
                if not contains then
                    diagonals[#diagonals + 1] = { polygon[previous], polygon[nextIndex] }
                    table.remove(indices, k)
                    clipped = true
                    break
                end
            end
        end
        if not clipped then
            return nil, "耳切失败（可能是非简单或非平面多边形）"
        end
        guard = guard + 1
        if guard > count * count then
            return nil, "耳切迭代超限"
        end
    end

    return diagonals
end

local function extractFeatureEdges(vertices, triA, triB, triC, triangleCount, angleDegrees)
    local requestedAngle = tonumber(angleDegrees) or 35
    local threshold = math.rad(math.max(0, math.min(179, requestedAngle)))
    local edgeMap = {}
    local edgeList = {}
    local edgeTotal = 0

    local function addFaceEdge(a, b, nx, ny, nz)
        local low, high = a, b
        if low > high then
            low, high = high, low
        end
        local key = low * INDEX_BASE + high
        local edge = edgeMap[key]
        if not edge then
            edgeTotal = edgeTotal + 1
            edge = {
                a = low,
                b = high,
                count = 1,
                n1x = nx,
                n1y = ny,
                n1z = nz,
                n2x = 0,
                n2y = 0,
                n2z = 0,
            }
            edgeMap[key] = edge
            edgeList[edgeTotal] = edge
        else
            edge.count = edge.count + 1
            if edge.count == 2 then
                edge.n2x, edge.n2y, edge.n2z = nx, ny, nz
            end
        end
    end

    for triangleIndex = 1, triangleCount do
        local ia = triA[triangleIndex]
        local ib = triB[triangleIndex]
        local ic = triC[triangleIndex]
        local baseA = ia * 3
        local baseB = ib * 3
        local baseC = ic * 3
        local ax, ay, az = vertices[baseA - 2], vertices[baseA - 1], vertices[baseA]
        local bx, by, bz = vertices[baseB - 2], vertices[baseB - 1], vertices[baseB]
        local cx, cy, cz = vertices[baseC - 2], vertices[baseC - 1], vertices[baseC]

        local ux, uy, uz = bx - ax, by - ay, bz - az
        local vx, vy, vz = cx - ax, cy - ay, cz - az
        local nx = uy * vz - uz * vy
        local ny = uz * vx - ux * vz
        local nz = ux * vy - uy * vx
        local normalLength = math.sqrt(nx * nx + ny * ny + nz * nz)
        if normalLength > 1e-12 then
            nx, ny, nz = nx / normalLength, ny / normalLength, nz / normalLength
        else
            nx, ny, nz = 0, 0, 0
        end

        addFaceEdge(ia, ib, nx, ny, nz)
        addFaceEdge(ib, ic, nx, ny, nz)
        addFaceEdge(ic, ia, nx, ny, nz)
    end

    local featureA, featureB = {}, {}
    local featureCount = 0
    for edgeIndex = 1, edgeTotal do
        local edge = edgeList[edgeIndex]
        local keep = edge.count == 1 or edge.count > 2
        if not keep and edge.count == 2 then
            local dot = edge.n1x * edge.n2x + edge.n1y * edge.n2y + edge.n1z * edge.n2z
            local angle = math.acos(math.max(0, math.min(1, math.abs(dot))))
            keep = angle >= threshold
        end
        if keep then
            featureCount = featureCount + 1
            featureA[featureCount] = edge.a
            featureB[featureCount] = edge.b
        end
    end
    return featureA, featureB, featureCount, edgeTotal
end

function Core.parseOBJ(text, options)
    options = options or {}
    if type(text) ~= "string" then
        return nil, "OBJ 内容必须是字符串"
    end
    if #text == 0 then
        return nil, "OBJ 内容为空"
    end

    local maxVertices = options.maxVertices or 1500000
    local maxFaces = options.maxFaces or 4000000
    local maxEdges = options.maxEdges or 1500000
    local yieldEvery = options.yieldEvery or 5000
    local yieldFn = options.yield
    local onProgress = options.onProgress
    local shouldCancel = options.shouldCancel
    local triangulate = options.triangulate == true
    local featureEdges = options.featureEdges == true
    local featureAngle = tonumber(options.featureAngle) or 35

    if text:sub(1, 3) == "\239\187\191" then
        text = text:sub(4)
    end
    local data = text:gsub("\r\n", "\n"):gsub("\r", "\n")
    local totalBytes = #data

    local vertices = {}
    local vertexCount = 0
    local edgeA, edgeB = {}, {}
    local edgeSet = {}
    local edgeCount = 0
    local faceCount = 0
    local triangleCount = 0
    local maxShellTriangles = options.maxShellTriangles or 30000
    local shellTriA, shellTriB, shellTriC = {}, {}, {}
    local shellTriangleCount = 0
    local shellTriangleOverflow = false
    local invalidVertexCount = 0
    local invalidFaceCount = 0
    local outOfRangeCount = 0
    local triangulationFailureCount = 0
    local warnings = {}
    local ctx = { warnings = warnings, warningCount = 0 }
    local fatalError = nil

    local bounds = { math.huge, math.huge, math.huge, -math.huge, -math.huge, -math.huge }

    local function addEdge(a, b)
        if a == b then
            return
        end
        local low, high = a, b
        if low > high then
            low, high = high, low
        end
        local key = low * INDEX_BASE + high
        if edgeSet[key] then
            return
        end
        edgeSet[key] = true
        edgeCount = edgeCount + 1
        edgeA[edgeCount] = low
        edgeB[edgeCount] = high
        if edgeCount > maxEdges then
            fatalError = string.format("解析边数超过上限 %d；可在 CONFIG 提高 MAX_PARSED_EDGES，或先用 Blender 减面/只导出轮廓", maxEdges)
        end
    end

    local function addShellTriangle(a, b, c)
        if a == b or b == c or a == c then
            return
        end
        if shellTriangleCount >= maxShellTriangles then
            shellTriangleOverflow = true
            return
        end
        shellTriangleCount = shellTriangleCount + 1
        shellTriA[shellTriangleCount] = a
        shellTriB[shellTriangleCount] = b
        shellTriC[shellTriangleCount] = c
    end

    local function addVertex(x, y, z)
        if vertexCount >= maxVertices then
            fatalError = string.format("顶点数超过上限 %d", maxVertices)
            return
        end
        vertexCount = vertexCount + 1
        local base = vertexCount * 3
        vertices[base - 2] = x
        vertices[base - 1] = y
        vertices[base] = z
        if x < bounds[1] then bounds[1] = x end
        if y < bounds[2] then bounds[2] = y end
        if z < bounds[3] then bounds[3] = z end
        if x > bounds[4] then bounds[4] = x end
        if y > bounds[5] then bounds[5] = y end
        if z > bounds[6] then bounds[6] = z end
    end

    local position = 1
    local lineNumber = 0
    while position <= totalBytes do
        local newline = string.find(data, "\n", position, true)
        local line
        if newline then
            line = string.sub(data, position, newline - 1)
            position = newline + 1
        else
            line = string.sub(data, position)
            position = totalBytes + 1
        end
        lineNumber = lineNumber + 1

        local hash = string.find(line, "#", 1, true)
        if hash then
            line = string.sub(line, 1, hash - 1)
        end
        line = string.match(line, "^%s*(.-)%s*$")

        if line ~= "" then
            local tag, rest = string.match(line, "^(%S+)%s*(.*)$")
            if tag then
                tag = string.lower(tag)
                if tag == "v" then
                    local sx, sy, sz = string.match(rest, "^(%S+)%s+(%S+)%s+(%S+)")
                    local x, y, z = tonumber(sx or ""), tonumber(sy or ""), tonumber(sz or "")
                    if not isFiniteNumber(x) or not isFiniteNumber(y) or not isFiniteNumber(z) then
                        invalidVertexCount = invalidVertexCount + 1
                        addWarning(ctx, lineNumber, "顶点坐标无效，已忽略")
                    else
                        addVertex(x, y, z)
                    end
                elseif tag == "f" then
                    local polygon = {}
                    local seen = {}
                    local bad = false
                    local outOfRange = false
                    for token in string.gmatch(rest, "%S+") do
                        local index, reason = parseFaceIndex(token, vertexCount)
                        if not index then
                            bad = true
                            if reason == "索引越界" or reason == "负索引越界" then
                                outOfRange = true
                            end
                            break
                        end
                        polygon[#polygon + 1] = index
                    end

                    if bad then
                        invalidFaceCount = invalidFaceCount + 1
                        if outOfRange then
                            outOfRangeCount = outOfRangeCount + 1
                        end
                        addWarning(ctx, lineNumber, "面包含无效索引，整面已跳过")
                    else
                        if #polygon > 1 and polygon[1] == polygon[#polygon] then
                            table.remove(polygon)
                        end
                        local duplicate = false
                        for i = 1, #polygon do
                            if seen[polygon[i]] then
                                duplicate = true
                                break
                            end
                            seen[polygon[i]] = true
                        end
                        if duplicate then
                            invalidFaceCount = invalidFaceCount + 1
                            addWarning(ctx, lineNumber, "面包含重复顶点，已跳过")
                        elseif #polygon < 3 then
                            invalidFaceCount = invalidFaceCount + 1
                            addWarning(ctx, lineNumber, "面顶点少于 3 个，已跳过")
                        else
                            faceCount = faceCount + 1
                            triangleCount = triangleCount + (#polygon - 2)
                            local first = polygon[1]
                            for i = 2, #polygon - 1 do
                                addShellTriangle(first, polygon[i], polygon[i + 1])
                            end
                            for i = 1, #polygon do
                                addEdge(polygon[i], polygon[i % #polygon + 1])
                            end
                            if triangulate and #polygon > 3 then
                                local diagonals, reason = triangulatePolygon(vertices, polygon)
                                if diagonals then
                                    for i = 1, #diagonals do
                                        addEdge(diagonals[i][1], diagonals[i][2])
                                    end
                                else
                                    triangulationFailureCount = triangulationFailureCount + 1
                                    addWarning(ctx, lineNumber, "三角化失败，仅保留边界: " .. tostring(reason))
                                end
                            end
                        end
                    end
                end
            end
        end

        if yieldEvery and yieldEvery > 0 and lineNumber % yieldEvery == 0 then
            if shouldCancel and shouldCancel() then
                return nil, "已取消"
            end
            if onProgress then
                onProgress(math.min(position, totalBytes), totalBytes)
            end
            if yieldFn then
                yieldFn()
            end
        end

        if faceCount > maxFaces then
            fatalError = string.format("面数超过上限 %d", maxFaces)
        end
        if fatalError then
            break
        end
    end

    if fatalError then
        return nil, fatalError
    end
    if vertexCount == 0 then
        return nil, "未找到任何顶点（v）"
    end
    if faceCount == 0 then
        return nil, "未找到任何有效面（f）"
    end
    if edgeCount == 0 then
        return nil, "未提取到任何唯一边"
    end

    local sourceEdgeCount = edgeCount
    local featureInfo = nil
    if featureEdges then
        local featureA, featureB, featureCount, featureEdgeTotal = extractFeatureEdges(
            vertices,
            shellTriA,
            shellTriB,
            shellTriC,
            shellTriangleCount,
            featureAngle
        )
        if featureCount == 0 then
            return nil, string.format(
                "边框检测没有找到特征边（角度阈值 %.0f°）。请降低阈值，或关闭边框模式查看全部边",
                featureAngle
            )
        end
        edgeA, edgeB, edgeCount = featureA, featureB, featureCount
        featureInfo = {
            sourceEdgeCount = sourceEdgeCount,
            edgeCount = featureCount,
            scannedEdgeCount = featureEdgeTotal,
            angle = featureAngle,
            triangleCount = shellTriangleCount,
            truncated = shellTriangleOverflow,
        }
        if shellTriangleOverflow then
            ctx.warningCount = ctx.warningCount + 1
            warnings[#warnings + 1] = string.format(
                "边框模式只扫描了前 %d 个三角形，较大模型可能漏掉少量边框",
                shellTriangleCount
            )
        end
    end

    local sizeX = bounds[4] - bounds[1]
    local sizeY = bounds[5] - bounds[2]
    local sizeZ = bounds[6] - bounds[3]

    if onProgress then
        onProgress(totalBytes, totalBytes)
    end

    return {
        vertices = vertices,
        vertexCount = vertexCount,
        edgeA = edgeA,
        edgeB = edgeB,
        edgeCount = edgeCount,
        sourceEdgeCount = sourceEdgeCount,
        featureInfo = featureInfo,
        faceCount = faceCount,
        triangleCount = triangleCount,
        shellTriA = shellTriA,
        shellTriB = shellTriB,
        shellTriC = shellTriC,
        shellTriangleCount = shellTriangleCount,
        shellTriangleOverflow = shellTriangleOverflow,
        bounds = bounds,
        center = {
            (bounds[1] + bounds[4]) * 0.5,
            (bounds[2] + bounds[5]) * 0.5,
            (bounds[3] + bounds[6]) * 0.5,
        },
        size = { sizeX, sizeY, sizeZ },
        warnings = warnings,
        warningCount = ctx.warningCount,
        invalidVertexCount = invalidVertexCount,
        invalidFaceCount = invalidFaceCount,
        outOfRangeCount = outOfRangeCount,
        triangulationFailureCount = triangulationFailureCount,
        triangulated = triangulate,
        sourceBytes = totalBytes,
        lineCount = lineNumber,
    }
end

local function buildClusters(model, cellSize)
    local vertices = model.vertices
    local vertexCount = model.vertexCount
    local bounds = model.bounds
    local minX, minY, minZ = bounds[1], bounds[2], bounds[3]
    cellSize = math.max(cellSize, 1e-12)

    local cells = {}
    local cellList = {}
    local cellCount = 0
    local vertexCell = {}

    for i = 1, vertexCount do
        local base = i * 3
        local x, y, z = vertices[base - 2], vertices[base - 1], vertices[base]
        local cx = math.floor((x - minX) / cellSize)
        local cy = math.floor((y - minY) / cellSize)
        local cz = math.floor((z - minZ) / cellSize)

        local xmap = cells[cx]
        if not xmap then
            xmap = {}
            cells[cx] = xmap
        end
        local ymap = xmap[cy]
        if not ymap then
            ymap = {}
            xmap[cy] = ymap
        end
        local cell = ymap[cz]
        if not cell then
            cellCount = cellCount + 1
            cell = { id = cellCount, sx = 0, sy = 0, sz = 0, n = 0 }
            ymap[cz] = cell
            cellList[cellCount] = cell
        end

        vertexCell[i] = cell.id
        cell.sx = cell.sx + x
        cell.sy = cell.sy + y
        cell.sz = cell.sz + z
        cell.n = cell.n + 1
    end

    return vertexCell, cellList, cellCount
end

local function countClusteredEdges(model, cellSize)
    local vertexCell = buildClusters(model, cellSize)
    local pairSet = {}
    local count = 0
    local edgeA, edgeB = model.edgeA, model.edgeB
    for i = 1, model.edgeCount do
        local c1 = vertexCell[edgeA[i]]
        local c2 = vertexCell[edgeB[i]]
        if c1 ~= c2 then
            local low, high = c1, c2
            if low > high then
                low, high = high, low
            end
            local key = low * INDEX_BASE + high
            if not pairSet[key] then
                pairSet[key] = true
                count = count + 1
            end
        end
    end
    return count
end

function Core.simplifyModel(model, targetEdges, options)
    options = options or {}
    if type(model) ~= "table" or not model.vertices or not model.edgeA then
        return nil, "模型数据无效"
    end
    local requestedTarget = nil
    if targetEdges ~= nil then
        requestedTarget = tonumber(targetEdges)
    end
    targetEdges = requestedTarget and math.floor(requestedTarget) or 0
    if targetEdges < 1 then
        return nil, "简化目标必须大于 0"
    end
    if model.edgeCount <= targetEdges then
        return nil, "当前边数未超过目标，无需简化"
    end

    local bounds = model.bounds
    local dx = bounds[4] - bounds[1]
    local dy = bounds[5] - bounds[2]
    local dz = bounds[6] - bounds[3]
    local diagonal = math.sqrt(dx * dx + dy * dy + dz * dz)
    if not isFiniteNumber(diagonal) or diagonal <= 0 then
        return nil, "模型包围盒无效"
    end

    local yieldFn = options.yield
    local onProgress = options.onProgress
    local shouldCancel = options.shouldCancel
    local iterations = options.iterations or 14
    local low = 0
    local high = diagonal
    local best = nil

    for iteration = 1, iterations do
        if shouldCancel and shouldCancel() then
            return nil, "已取消"
        end
        local middle = (low + high) * 0.5
        local count = countClusteredEdges(model, middle)
        if count <= targetEdges then
            best = middle
            high = middle
        else
            low = middle
        end
        if onProgress then
            onProgress(iteration, iterations)
        end
        if yieldFn then
            yieldFn()
        end
    end

    if not best then
        return nil, "无法在目标上限内完成简化"
    end

    local vertexCell, cellList = buildClusters(model, best)
    local pairSet = {}
    local result = {
        count = 0,
        ax = {}, ay = {}, az = {},
        bx = {}, by = {}, bz = {},
        gridSize = best,
        sourceEdgeCount = model.edgeCount,
    }

    for i = 1, model.edgeCount do
        if shouldCancel and i % 5000 == 0 and shouldCancel() then
            return nil, "已取消"
        end
        local c1 = vertexCell[model.edgeA[i]]
        local c2 = vertexCell[model.edgeB[i]]
        if c1 ~= c2 then
            local lowCell, highCell = c1, c2
            if lowCell > highCell then
                lowCell, highCell = highCell, lowCell
            end
            local key = lowCell * INDEX_BASE + highCell
            if not pairSet[key] then
                local p1 = cellList[c1]
                local p2 = cellList[c2]
                local ax = p1.sx / p1.n
                local ay = p1.sy / p1.n
                local az = p1.sz / p1.n
                local bx = p2.sx / p2.n
                local by = p2.sy / p2.n
                local bz = p2.sz / p2.n
                local edgeX, edgeY, edgeZ = bx - ax, by - ay, bz - az
                if edgeX * edgeX + edgeY * edgeY + edgeZ * edgeZ > 1e-18 then
                    pairSet[key] = true
                    local n = result.count + 1
                    result.count = n
                    result.ax[n] = ax
                    result.ay[n] = ay
                    result.az[n] = az
                    result.bx[n] = bx
                    result.by[n] = by
                    result.bz[n] = bz
                end
            end
        end
    end

    if result.count == 0 then
        local sampled, sampleError = Core.sampleEdges(model, targetEdges, options)
        if not sampled then
            return nil, sampleError
        end
        return sampled
    end
    return result
end

function Core.sampleEdges(model, targetEdges, options)
    options = options or {}
    local requestedTarget = nil
    if targetEdges ~= nil then
        requestedTarget = tonumber(targetEdges)
    end
    targetEdges = requestedTarget and math.floor(requestedTarget) or 0
    if targetEdges < 1 then
        return nil, "采样目标必须大于 0"
    end
    if targetEdges >= model.edgeCount then
        return Core.buildRenderEdges(model, nil, false)
    end

    local shouldCancel = options.shouldCancel
    local result = {
        count = targetEdges,
        ax = {}, ay = {}, az = {},
        bx = {}, by = {}, bz = {},
        sourceEdgeCount = model.edgeCount,
        sampled = true,
    }
    local step = model.edgeCount / targetEdges
    local vertices = model.vertices
    for i = 1, targetEdges do
        if shouldCancel and i % 5000 == 0 and shouldCancel() then
            return nil, "已取消"
        end
        local sourceIndex = math.floor((i - 0.5) * step) + 1
        if sourceIndex > model.edgeCount then
            sourceIndex = model.edgeCount
        end
        local a = model.edgeA[sourceIndex] * 3
        local b = model.edgeB[sourceIndex] * 3
        result.ax[i] = vertices[a - 2]
        result.ay[i] = vertices[a - 1]
        result.az[i] = vertices[a]
        result.bx[i] = vertices[b - 2]
        result.by[i] = vertices[b - 1]
        result.bz[i] = vertices[b]
    end
    return result
end

function Core.buildRenderEdges(model, maxEdges, allowSimplify, options)
    if type(model) ~= "table" or not model.edgeA or not model.edgeB then
        return nil, "模型数据无效"
    end

    if maxEdges ~= nil then
        maxEdges = tonumber(maxEdges)
    end
    if maxEdges and maxEdges > 0 then
        maxEdges = math.floor(maxEdges)
        if model.edgeCount > maxEdges then
            if not allowSimplify then
                return nil, string.format(
                    "边数 %d 超过上限 %d；请提高上限或启用自动简化",
                    model.edgeCount,
                    maxEdges
                )
            end
            return Core.simplifyModel(model, maxEdges, options)
        end
    end

    local result = {
        count = model.edgeCount,
        ax = {}, ay = {}, az = {},
        bx = {}, by = {}, bz = {},
        sourceEdgeCount = model.edgeCount,
    }
    local vertices = model.vertices
    for i = 1, model.edgeCount do
        local a = model.edgeA[i] * 3
        local b = model.edgeB[i] * 3
        result.ax[i] = vertices[a - 2]
        result.ay[i] = vertices[a - 1]
        result.az[i] = vertices[a]
        result.bx[i] = vertices[b - 2]
        result.by[i] = vertices[b - 1]
        result.bz[i] = vertices[b]
    end
    return result
end

function Core.computeEdgeBasis(ax, ay, az, bx, by, bz)
    local dx, dy, dz = bx - ax, by - ay, bz - az
    local length = math.sqrt(dx * dx + dy * dy + dz * dz)
    if not isFiniteNumber(length) or length < 1e-9 then
        return nil
    end

    local ux, uy, uz = dx / length, dy / length, dz / length

    local rx, ry, rz
    if math.abs(uy) < 0.99 then
        rx, ry, rz = 0, 1, 0
    else
        rx, ry, rz = 1, 0, 0
    end

    local zx = uy * rz - uz * ry
    local zy = uz * rx - ux * rz
    local zz = ux * ry - uy * rx
    local zLength = math.sqrt(zx * zx + zy * zy + zz * zz)
    if zLength < 1e-9 then
        return nil
    end
    zx, zy, zz = zx / zLength, zy / zLength, zz / zLength

    local yx = zy * uz - zz * uy
    local yy = zz * ux - zx * uz
    local yz = zx * uy - zy * ux
    local yLength = math.sqrt(yx * yx + yy * yy + yz * yz)
    if yLength < 1e-9 then
        return nil
    end
    yx, yy, yz = yx / yLength, yy / yLength, yz / yLength

    return {
        length = length,
        mx = (ax + bx) * 0.5,
        my = (ay + by) * 0.5,
        mz = (az + bz) * 0.5,
        xx = ux, xy = uy, xz = uz,
        yx = yx, yy = yy, yz = yz,
        zx = zx, zy = zy, zz = zz,
    }
end

local Players = game:GetService("Players")
local Workspace = game:GetService("Workspace")
local UserInputService = game:GetService("UserInputService")
local ReplicatedStorage = game:GetService("ReplicatedStorage")
local TweenService = game:GetService("TweenService")

local LocalPlayer = Players.LocalPlayer
if not LocalPlayer then
    warn("[OBJ Wireframe] 找不到 LocalPlayer。请在客户端 LocalScript 或执行器中运行。")
    return
end

local PlayerGui = LocalPlayer:WaitForChild("PlayerGui", 30)
if not PlayerGui then
    warn("[OBJ Wireframe] 找不到 PlayerGui，界面无法创建。")
    return
end

local CONFIG = {
    VERSION = Core.VERSION,
    UI_VERSION = "2.3.7",

    MAX_FILE_BYTES = 128 * 1024 * 1024,
    MAX_VERTICES = 1500000,
    MAX_FACES = 4000000,
    MAX_PARSED_EDGES = 1500000,
    PARSE_YIELD_LINES = 4000,

    DEFAULT_MAX_EDGES = 15000,
    HARD_MAX_EDGES = 50000,
    BATCH_SIZE = 220,
    MIN_PART_SIZE = 0.05,
    MAX_PART_LENGTH = 2048,
    DEFAULT_THICKNESS = 0.08,
    DEFAULT_TARGET_SIZE = 30,
    DEFAULT_COLOR = Color3.fromRGB(0, 220, 255),
    MATERIAL = Enum.Material.SmoothPlastic,
    FOLDER_PREFIX = "OBJ_Wireframe_",

    PREVIEW_MAX_EDGES = 50000,
    PREVIEW_BATCH = 180,
    PREVIEW_AXIS_LENGTH = 8,
    PREVIEW_COLOR = Color3.fromRGB(0, 220, 255),
    PREVIEW_TRANSPARENCY = 0.62,
    PREVIEW_DEBOUNCE = 0.35,

    ACTUAL_BLOCK_NAME = "PlasticBlock",
    ACTUAL_TOOL_BUILD = "BuildingTool",
    ACTUAL_TOOL_SCALE = "ScalingTool",
    ACTUAL_TOOL_DELETE = "DeleteTool",
    ACTUAL_STAGE_Y = 5000,
    ACTUAL_STAGE_GAP = 4,
    ACTUAL_STAGE_COLS = 1,
    ACTUAL_PLACE_BATCH = 50,
    ACTUAL_PLACE_BATCH_WAIT = 0.05,
    ACTUAL_PLACE_MAX_IN_FLIGHT = 400,
    ACTUAL_PLACE_TICK = 0.02,
    ACTUAL_PLACE_STALL_SECONDS = 20,
    ACTUAL_SCALE_MAX_IN_FLIGHT = 50,
    ACTUAL_SCALE_RATE = 1000,
    ACTUAL_SCALE_TICK = 0.05,
    ACTUAL_MATCH_TOLERANCE = 4,
    ACTUAL_RETRY_PASSES = 2,
    ACTUAL_VERIFY_TOLERANCE = 1.5,
    ACTUAL_DELETE_MAX_IN_FLIGHT = 120,
    ACTUAL_DELETE_TICK = 0.03,
    ACTUAL_CONFIRM_BLOCK_THRESHOLD = 200,
    ACTUAL_ARM_SECONDS = 10,
    CLEAR_AREA_ARM_SECONDS = 6,

    DEFAULT_FEATURE_EDGE_ANGLE = 35,
    MIN_FEATURE_EDGE_ANGLE = 0,
    MAX_FEATURE_EDGE_ANGLE = 179,

    MAX_SHELL_TRIANGLES = 30000,
    SHELL_VOXEL_OVERLAP = 1.5,
    SHELL_SURFACE_REACH = 0.95,
    SHELL_MAX_CELLS_PER_TRIANGLE = 65536,
    SHELL_BEVEL_ENABLED = true,
    SHELL_BEVEL_ANGLE = 15,
    SHELL_BEVEL_WIDTH = 2.5,
    SHELL_BEVEL_SEGMENT = 1.0,
    DEFAULT_SHELL_PLATE_SIZE = 0.5,
    MIN_SHELL_PLATE_SIZE = 0.2,
    MAX_SHELL_PLATE_SIZE = 20,
    DEFAULT_SHELL_THICKNESS = 0.08,
    DEFAULT_SHELL_BUDGET = 40000,
    MAX_SHELL_BUDGET = 50000,

    WINDOW_SIZE = Vector2.new(760, 726),
    WINDOW_MIN = Vector2.new(600, 460),
    WINDOW_MAX = Vector2.new(1010, 900),
    RAIL_WIDTH = 150,
    HEADER_HEIGHT = 58,
    STATUS_HEIGHT = 68,
    TOAST_SECONDS = 6,
    LOG_LIMIT = 150,
    ANIM = 0.16,
}

local THEME = {
    base = Color3.fromRGB(244, 244, 246),
    rail = Color3.fromRGB(237, 237, 240),
    surface = Color3.fromRGB(255, 255, 255),
    raised = Color3.fromRGB(240, 240, 243),
    inset = Color3.fromRGB(247, 247, 249),
    hover = Color3.fromRGB(230, 230, 234),

    line = Color3.fromRGB(201, 201, 208),
    lineSoft = Color3.fromRGB(228, 228, 233),

    text = Color3.fromRGB(14, 14, 17),
    textDim = Color3.fromRGB(67, 67, 75),
    textFaint = Color3.fromRGB(99, 99, 108),

    accent = Color3.fromRGB(20, 20, 24),
    accentAlt = Color3.fromRGB(52, 52, 60),
    accentSoft = Color3.fromRGB(232, 232, 236),
    accentText = Color3.fromRGB(255, 255, 255),

    ok = Color3.fromRGB(52, 52, 58),
    warn = Color3.fromRGB(24, 24, 28),
    err = Color3.fromRGB(0, 0, 0),
    errSoft = Color3.fromRGB(243, 243, 245),

    axisX = Color3.fromRGB(14, 14, 17),
    axisY = Color3.fromRGB(104, 104, 113),
    axisZ = Color3.fromRGB(158, 158, 166),

    white = Color3.fromRGB(255, 255, 255),
    black = Color3.fromRGB(0, 0, 0),
    cardTop = Color3.fromRGB(255, 255, 255),
    inputTop = Color3.fromRGB(250, 250, 252),
    scrim = Color3.fromRGB(10, 10, 12),
    shadow = Color3.fromRGB(0, 0, 0),
}

local function isFinite(value)
    return type(value) == "number"
        and value == value
        and value ~= math.huge
        and value ~= -math.huge
end

local function clamp(value, minimum, maximum)
    if not isFinite(value) then
        value = minimum or 0
    end
    if minimum and value < minimum then
        value = minimum
    end
    if maximum and value > maximum then
        value = maximum
    end
    return value
end

local function formatNumber(value)
    if not isFinite(value) then
        return "0"
    end
    if value == math.floor(value) and math.abs(value) < 1e15 then
        return string.format("%d", value)
    end
    return string.format("%.6g", value)
end

local function normalizeSlashes(path)
    return (tostring(path or ""):gsub("\\", "/"))
end

local function cleanPath(text)
    local path = tostring(text or "")
    path = string.match(path, "^%s*(.-)%s*$") or ""
    if #path >= 2 then
        local first = string.sub(path, 1, 1)
        local last = string.sub(path, -1)
        if (first == '"' and last == '"') or (first == "'" and last == "'") then
            path = string.sub(path, 2, -2)
        end
    end
    return path
end

local function trimText(text)
    return (string.match(tostring(text or ""), "^%s*(.-)%s*$")) or ""
end

local function entryNameOf(path)
    return string.match(normalizeSlashes(path), "([^/]+)$") or tostring(path)
end

local function joinPath(directory, entry)
    local dir = normalizeSlashes(directory):gsub("/+$", "")
    local child = normalizeSlashes(entry):gsub("^/+", "")
    if dir == "" or dir == "." then
        return child
    end
    if string.sub(child, 1, #dir + 1) == dir .. "/" then
        return child
    end
    if string.find(child, "/", 1, true) then
        return child
    end
    return dir .. "/" .. child
end

local function shorten(text, limit)
    text = tostring(text or "")
    if #text <= limit then
        return text
    end
    return string.sub(text, 1, limit - 1) .. "…"
end

local EXECUTOR_ENV = nil
do
    local ok, environment = pcall(function()
        if type(getgenv) == "function" then
            return getgenv()
        end
        return nil
    end)
    if ok and type(environment) == "table" then
        EXECUTOR_ENV = environment
    end
end

local DIRECT_GLOBALS = {
    readfile = function()
        return readfile
    end,
    listfiles = function()
        return listfiles
    end,
    isfolder = function()
        return isfolder
    end,
    isfile = function()
        return isfile
    end,
    identifyexecutor = function()
        return identifyexecutor
    end,
}

local function resolveFunction(name)
    local direct = DIRECT_GLOBALS[name]
    if direct then
        local ok, value = pcall(direct)
        if ok and type(value) == "function" then
            return value
        end
    end
    if EXECUTOR_ENV and type(EXECUTOR_ENV[name]) == "function" then
        return EXECUTOR_ENV[name]
    end
    local ok, value = pcall(function()
        return _G[name]
    end)
    if ok and type(value) == "function" then
        return value
    end
    return nil
end

local CAPS = {
    readfile = resolveFunction("readfile"),
    listfiles = resolveFunction("listfiles"),
    isfolder = resolveFunction("isfolder"),
    isfile = resolveFunction("isfile"),
    identifyexecutor = resolveFunction("identifyexecutor"),
}

local executorName = "Roblox Client"
if CAPS.identifyexecutor then
    local ok, name = pcall(CAPS.identifyexecutor)
    if ok and type(name) == "string" and name ~= "" then
        executorName = name
    end
end

local canBrowseWorkspace = (CAPS.listfiles ~= nil) and (CAPS.isfolder ~= nil)

local nativePartCreationOk = false
do
    local ok, result = pcall(function()
        local part = Instance.new("Part")
        part.Anchored = true
        part.CanCollide = false
        part.CanTouch = false
        part.CanQuery = false
        part.Size = Vector3.new(1, 1, 1)
        part.CFrame = CFrame.new(0, 0, 0)
        part:Destroy()
        return true
    end)
    nativePartCreationOk = (ok and result == true)
end

print(string.format(
    "[OBJ Wireframe] 环境：executor=%s readfile=%s listfiles=%s partCreate=%s",
    executorName,
    tostring(CAPS.readfile ~= nil),
    tostring(CAPS.listfiles ~= nil),
    tostring(nativePartCreationOk)
))

local State = {
    model = nil,
    sourceText = nil,
    sourceName = nil,
    needsReparse = false,

    parsing = false,
    generating = false,
    actualBuilding = false,
    previewBuilding = false,
    previewPending = false,
    cancelRequested = false,
    clearOnCancel = false,

    folder = nil,
    generatedCount = 0,
    lastSimplifyInfo = nil,

    pivotMode = "center",

    previewFolder = nil,
    previewVisible = false,
    previewToken = 0,
    previewRender = nil,
    previewRenderModel = nil,
    previewRenderLimit = nil,
    lastPreviewSimplifyInfo = nil,

    actualBlocks = {},
    actualBuildToken = 0,
    buildArmed = false,
    clearAreaArmed = false,

    activeTab = 1,
    minimized = false,
    windowSize = CONFIG.WINDOW_SIZE,
    windowHidden = false,
}

local function isBusy()
    return State.parsing or State.generating or State.actualBuilding
end

local function busyReason()
    if State.parsing then
        return "解析 OBJ"
    end
    if State.generating then
        return "生成本地线框"
    end
    if State.actualBuilding then
        return "实际建造"
    end
    return nil
end

local Log = {
    entries = {},
    limit = CONFIG.LOG_LIMIT,
    onAppend = nil,
}

function Log.add(text, kind)
    local entry = {
        time = os.date("%H:%M:%S"),
        text = tostring(text or ""),
        kind = kind or "info",
    }
    local list = Log.entries
    list[#list + 1] = entry
    while #list > Log.limit do
        table.remove(list, 1)
    end
    if Log.onAppend then
        pcall(Log.onAppend, entry)
    end
    return entry
end

function Log.clear()
    Log.entries = {}
    if Log.onAppend then
        pcall(Log.onAppend, nil)
    end
end

local UI = {}
local App = {}

local Kit = {}

local TONES = {
    primary = {
        fillA = Color3.fromRGB(28, 28, 33),
        fillB = Color3.fromRGB(0, 0, 0),
        text = Color3.fromRGB(255, 255, 255),
        stroke = Color3.fromRGB(0, 0, 0),
        strokeAlpha = 0.2,
        bold = true,
    },
    default = {
        fillA = Color3.fromRGB(255, 255, 255),
        fillB = Color3.fromRGB(244, 244, 247),
        text = Color3.fromRGB(14, 14, 17),
        stroke = THEME.line,
        strokeAlpha = 0.1,
    },
    quiet = {
        fillA = Color3.fromRGB(243, 243, 246),
        fillB = Color3.fromRGB(235, 235, 239),
        text = Color3.fromRGB(14, 14, 17),
        stroke = THEME.lineSoft,
        strokeAlpha = 0.15,
    },
    danger = {
        fillA = Color3.fromRGB(255, 255, 255),
        fillB = Color3.fromRGB(246, 246, 248),
        text = Color3.fromRGB(0, 0, 0),
        stroke = Color3.fromRGB(120, 120, 128),
        strokeAlpha = 0.25,
        bold = true,
    },
    chip = {
        fillA = Color3.fromRGB(255, 255, 255),
        fillB = Color3.fromRGB(244, 244, 247),
        text = Color3.fromRGB(14, 14, 17),
        stroke = THEME.line,
        strokeAlpha = 0.2,
    },
    ghost = {
        fillA = Color3.fromRGB(250, 250, 251),
        fillB = Color3.fromRGB(246, 246, 248),
        text = Color3.fromRGB(92, 92, 101),
        stroke = THEME.lineSoft,
        strokeAlpha = 0.35,
    },
}

local function safeTween(object, props, time, style, direction)
    if not object or not object.Parent then
        return false
    end
    local ok, result = pcall(function()
        local tween = TweenService:Create(
            object,
            TweenInfo.new(
                time or CONFIG.ANIM,
                style or Enum.EasingStyle.Quad,
                direction or Enum.EasingDirection.Out
            ),
            props
        )
        tween:Play()
        return tween
    end)
    return ok
end

Kit.tween = safeTween

function Kit.new(className, props)
    local object = Instance.new(className)
    if props then
        for key, value in pairs(props) do
            if key ~= "Parent" then
                object[key] = value
            end
        end
        if props.Parent then
            object.Parent = props.Parent
        end
    end
    return object
end

function Kit.round(object, radius)
    local corner = Instance.new("UICorner")
    corner.CornerRadius = UDim.new(0, radius or 8)
    corner.Parent = object
    return corner
end

function Kit.outline(object, color, thickness, transparency)
    local stroke = Instance.new("UIStroke")
    stroke.Color = color or THEME.line
    stroke.Thickness = thickness or 1
    stroke.Transparency = transparency or 0.4
    stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
    stroke.Parent = object
    return stroke
end

function Kit.edge(object, color, transparency)
    local stroke = Instance.new("UIStroke")
    stroke.Color = color or THEME.line
    stroke.Thickness = 1
    stroke.Transparency = transparency or 0.35
    stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
    stroke.Parent = object
    return stroke
end

function Kit.fill(object, colorA, colorB, rotation)
    local gradient = Instance.new("UIGradient")
    gradient.Rotation = rotation or 90
    gradient.Color = ColorSequence.new(colorA or THEME.surface, colorB or THEME.surface)
    gradient.Parent = object
    return gradient
end

function Kit.padding(object, top, right, bottom, left)
    local padding = Instance.new("UIPadding")
    padding.PaddingTop = UDim.new(0, top or 0)
    padding.PaddingRight = UDim.new(0, right or top or 0)
    padding.PaddingBottom = UDim.new(0, bottom or top or 0)
    padding.PaddingLeft = UDim.new(0, left or right or top or 0)
    padding.Parent = object
    return padding
end

function Kit.vlist(parent, gap)
    local layout = Instance.new("UIListLayout")
    layout.FillDirection = Enum.FillDirection.Vertical
    layout.Padding = UDim.new(0, gap or 6)
    layout.SortOrder = Enum.SortOrder.LayoutOrder
    layout.HorizontalAlignment = Enum.HorizontalAlignment.Center
    layout.VerticalAlignment = Enum.VerticalAlignment.Top
    layout.Parent = parent
    return layout
end

function Kit.hlist(parent, gap)
    local layout = Instance.new("UIListLayout")
    layout.FillDirection = Enum.FillDirection.Horizontal
    layout.Padding = UDim.new(0, gap or 6)
    layout.SortOrder = Enum.SortOrder.LayoutOrder
    layout.VerticalAlignment = Enum.VerticalAlignment.Center
    layout.HorizontalAlignment = Enum.HorizontalAlignment.Left
    layout.Parent = parent
    return layout
end

function Kit.label(parent, text, opts)
    opts = opts or {}
    local label = Instance.new("TextLabel")
    label.BackgroundTransparency = 1
    label.BorderSizePixel = 0
    label.Font = opts.bold and Enum.Font.GothamBold or Enum.Font.Gotham
    label.Text = text or ""
    label.TextColor3 = opts.color or THEME.text
    label.TextSize = opts.size or 12
    label.TextXAlignment = opts.align or Enum.TextXAlignment.Left
    label.TextYAlignment = opts.valign or Enum.TextYAlignment.Center
    label.RichText = false
    if opts.wrap then
        label.TextWrapped = true
        label.Size = UDim2.new(1, 0, 0, 0)
        label.AutomaticSize = Enum.AutomaticSize.Y
    else
        label.TextWrapped = false
        label.TextTruncate = Enum.TextTruncate.AtEnd
        label.Size = UDim2.new(1, 0, 0, opts.height or 18)
    end
    label.LayoutOrder = opts.order or 0
    label.ZIndex = opts.zIndex or 2
    label.Parent = parent
    return label
end

function Kit.hint(parent, text, order)
    return Kit.label(parent, text, {
        wrap = true,
        size = 11,
        color = THEME.textFaint,
        valign = Enum.TextYAlignment.Top,
        order = order or 0,
    })
end

function Kit.card(parent, title, order, opts)
    opts = opts or {}
    local card = Instance.new("Frame")
    card.Name = "Card_" .. tostring(title or order or "x")
    card.BackgroundColor3 = THEME.surface
    card.BackgroundTransparency = opts.transparency or 0.02
    card.BorderSizePixel = 0
    card.Size = UDim2.new(1, 0, 0, 0)
    card.AutomaticSize = Enum.AutomaticSize.Y
    card.LayoutOrder = order or 0
    card.Parent = parent
    Kit.round(card, 12)
    Kit.edge(card, THEME.line, 0.1, 0.7)
    Kit.fill(card, THEME.cardTop, THEME.surface)
    Kit.padding(card, 12, 12, 12, 12)
    Kit.vlist(card, 8)

    if title and title ~= "" then
        local head = Instance.new("Frame")
        head.Name = "CardHeader"
        head.BackgroundTransparency = 1
        head.Size = UDim2.new(1, 0, 0, 18)
        head.LayoutOrder = 0
        head.Parent = card

        local dot = Instance.new("Frame")
        dot.BackgroundColor3 = opts.accent or THEME.accent
        dot.BorderSizePixel = 0
        dot.Size = UDim2.fromOffset(3, 12)
        dot.Position = UDim2.new(0, 0, 0.5, 0)
        dot.AnchorPoint = Vector2.new(0, 0.5)
        dot.Parent = head
        Kit.round(dot, 2)

        local label = Kit.label(head, title, {
            bold = true,
            size = 12,
            color = THEME.text,
        })
        label.Position = UDim2.fromOffset(11, 0)
        label.Size = UDim2.new(1, -80, 1, 0)

        if opts.index then
            local badge = Kit.label(head, string.format("%02d", opts.index), {
                size = 10,
                color = THEME.textFaint,
            })
            badge.AnchorPoint = Vector2.new(1, 0.5)
            badge.Position = UDim2.new(1, 0, 0.5, 0)
            badge.Size = UDim2.fromOffset(28, 14)
            badge.TextXAlignment = Enum.TextXAlignment.Right
            badge.Font = Enum.Font.Code
        end
    end

    return card
end

function Kit.gap(parent, height, order)
    local spacer = Instance.new("Frame")
    spacer.BackgroundTransparency = 1
    spacer.Size = UDim2.new(1, 0, 0, height or 4)
    spacer.LayoutOrder = order or 0
    spacer.Parent = parent
    return spacer
end

function Kit.divider(parent, order)
    local line = Instance.new("Frame")
    line.BackgroundColor3 = THEME.lineSoft
    line.BorderSizePixel = 0
    line.Size = UDim2.new(1, 0, 0, 1)
    line.LayoutOrder = order or 0
    line.Parent = parent
    return line
end

function Kit.keyValue(parent, key, value, order)
    local row = Instance.new("Frame")
    row.BackgroundTransparency = 1
    row.Size = UDim2.new(1, 0, 0, 18)
    row.LayoutOrder = order or 0
    row.Parent = parent

    local left = Kit.label(row, key, { size = 11, color = THEME.textFaint })
    left.Size = UDim2.new(1, -120, 1, 0)

    local right = Kit.label(row, value, {
        size = 11,
        color = THEME.textDim,
        align = Enum.TextXAlignment.Right,
    })
    right.AnchorPoint = Vector2.new(1, 0)
    right.Position = UDim2.new(1, 0, 0, 0)
    right.Size = UDim2.fromOffset(118, 18)
    right.Font = Enum.Font.Code
    return row, right
end

local Button = {}
Button.__index = Button

local function paint(button)
    local tone = TONES[button.tone] or TONES.default
    local dimmed = button.dimmed

    local textColor = dimmed and THEME.textFaint or tone.text
    button.Instance.TextColor3 = textColor
    button.Instance.TextTransparency = 0
    button.Instance.Font = (tone.bold and not dimmed) and Enum.Font.GothamBold or Enum.Font.Gotham
    if button.Label then
        button.Label.TextColor3 = textColor
        button.Label.TextTransparency = 0
        button.Label.Font = (tone.bold and not dimmed)
            and Enum.Font.GothamBold
            or Enum.Font.Gotham
    end
    button.Instance.BackgroundColor3 = dimmed and THEME.raised or tone.fillA

    if button.Gradient then
        pcall(function()
            button.Gradient:Destroy()
        end)
        button.Gradient = nil
    end
    local function sweep(node)
        for _, child in ipairs(node:GetChildren()) do
            if child.ClassName == "UIGradient" then
                child:Destroy()
            else
                sweep(child)
            end
        end
    end
    sweep(button.Instance)

    if button.Stroke then
        button.Stroke.Color = dimmed and THEME.lineSoft or tone.stroke
        button.Stroke.Transparency = dimmed and 0.35 or tone.strokeAlpha
    end
end

local TONE_ALIAS = { accent = "primary" }

function Button:SetTone(tone)
    self.tone = TONE_ALIAS[tone or ""] or tone or "default"
    paint(self)
end

function Button:SetLabel(text)
    local value = tostring(text or "")
    self.Instance.Text = ""
    if self.Label then
        self.Label.Text = value
    end
end

function Button:GetLabel()
    if self.Label then
        return self.Label.Text
    end
    return self.Instance.Text
end

function Button:SetTextSize(size)
    self.Instance.TextSize = size
    if self.Label then
        self.Label.TextSize = size
    end
end

function Button:SetZIndex(zindex)
    self.Instance.ZIndex = zindex
    if self.Label then
        self.Label.ZIndex = zindex + 1
    end
end

function Button:SetDimmed(dimmed, reason)
    self.dimmed = dimmed and true or false
    self.blockedReason = reason
    paint(self)
end

function Button:SetBusy(busy)
    if busy == self.busy then
        return
    end
    self.busy = busy and true or false
    local target = self.Label or self.Instance
    safeTween(target, { TextTransparency = self.busy and 0.45 or 0 }, 0.12)
end

function Button:OnClick(callback)
    self.callback = callback
    self.Instance.MouseButton1Click:Connect(function()
        if self.dimmed then
            if self.blockedReason then
                App.status(self.blockedReason, "warn")
            end
            return
        end
        local ok, err = pcall(callback)
        if not ok then
            App.fail(self:GetLabel(), err)
        end
    end)
end

function Kit.button(parent, text, opts)
    opts = opts or {}
    local instance = Instance.new("TextButton")
    local tone = TONES[opts.tone or (opts.accent and "primary") or "default"] or TONES.default
    instance.BackgroundColor3 = tone.fillA
    instance.BorderSizePixel = 0
    instance.AutoButtonColor = false
    instance.Text = ""
    instance.TextColor3 = tone.text
    instance.Font = tone.bold and Enum.Font.GothamBold or Enum.Font.Gotham
    instance.TextSize = opts.size or 12
    instance.TextWrapped = false
    instance.TextTruncate = Enum.TextTruncate.AtEnd
    instance.Size = UDim2.new(1, 0, 0, opts.height or 32)
    instance.LayoutOrder = opts.order or 0
    instance.Parent = parent
    Kit.round(instance, 8)

    local label = Instance.new("TextLabel")
    label.Name = "ButtonLabel"
    label.BackgroundTransparency = 1
    label.BorderSizePixel = 0
    label.Size = UDim2.fromScale(1, 1)
    label.Text = tostring(text or "")
    label.TextColor3 = tone.text
    label.Font = tone.bold and Enum.Font.GothamBold or Enum.Font.Gotham
    label.TextSize = opts.size or 12
    label.TextWrapped = false
    label.TextTruncate = Enum.TextTruncate.AtEnd
    label.ZIndex = (instance.ZIndex or 1) + 1
    label.Parent = instance

    local function scrubGradients(root)
        for _, child in ipairs(root:GetChildren()) do
            if child.ClassName == "UIGradient" then
                child:Destroy()
            else
                scrubGradients(child)
            end
        end
    end

    local stroke = Kit.edge(instance, tone.stroke, 0.12)
    scrubGradients(instance)

    local pressScale = Instance.new("UIScale")
    pressScale.Scale = 1
    pressScale.Parent = instance

    local self = setmetatable({
        Instance = instance,
        Label = label,
        Stroke = stroke,
        Gradient = nil,
        PressScale = pressScale,
        tone = opts.tone or (opts.accent and "primary") or "default",
        dimmed = false,
        restSize = instance.Size,
    }, Button)
    paint(self)

    instance.MouseButton1Down:Connect(function()
        if not self.dimmed then
            safeTween(pressScale, { Scale = 0.965 }, 0.08)
        end
    end)
    instance.MouseButton1Up:Connect(function()
        safeTween(pressScale, { Scale = 1 }, 0.12,
            Enum.EasingStyle.Back, Enum.EasingDirection.Out)
    end)

    instance.MouseEnter:Connect(function()
        if self.dimmed then
            return
        end
        local current = TONES[self.tone] or TONES.default
        if self.tone == "primary" then
            safeTween(instance, {
                Size = UDim2.new(
                    self.restSize.X.Scale,
                    self.restSize.X.Offset,
                    self.restSize.Y.Scale,
                    self.restSize.Y.Offset - 1
                ),
            }, 0.12)
        else
            safeTween(instance, {
                BackgroundColor3 = opts.hoverFill or current.fillA:Lerp(THEME.hover, 0.35),
            }, 0.12)
        end
        if stroke then
            stroke.Transparency = 0.05
        end
    end)

    instance.MouseLeave:Connect(function()
        if self.dimmed then
            return
        end
        paint(self)
        safeTween(instance, {
            Size = UDim2.new(
                self.restSize.X.Scale,
                self.restSize.X.Offset,
                self.restSize.Y.Scale,
                self.restSize.Y.Offset
            ),
        }, 0.12)
    end)

    return self
end

function Kit.buttonRow(parent, definitions, opts)
    opts = opts or {}
    local gap = opts.gap or 8
    local height = opts.height or 32
    local row = Instance.new("Frame")
    row.BackgroundTransparency = 1
    row.Size = UDim2.new(1, 0, 0, height)
    row.LayoutOrder = opts.order or 0
    row.Parent = parent
    Kit.hlist(row, gap)

    local count = #definitions
    local buttons = {}
    for index, definition in ipairs(definitions) do
        local button = Kit.button(row, definition.text, {
            accent = definition.accent,
            tone = definition.tone,
            height = height,
            order = index,
        })
        button.Instance.Size = UDim2.new(
            1 / count,
            -(gap * (count - 1)) / count,
            1,
            0
        )
        button.restSize = button.Instance.Size
        if definition.onClick then
            button:OnClick(definition.onClick)
        end
        buttons[index] = button
    end
    return row, buttons
end

local Field = {}
Field.__index = Field

function Field:GetText()
    return self.Box.Text
end

function Field:SetText(text)
    self.Box.Text = tostring(text or "")
end

function Field:Number(minimum, maximum, fallback, integer)
    local value = tonumber(self.Box.Text)
    if not isFinite(value) then
        value = fallback
    end
    if value == nil then
        value = 0
    end
    if integer then
        value = math.floor(value)
    end
    return clamp(value, minimum, maximum)
end

function Field:Commit(minimum, maximum, fallback, integer)
    local value = self:Number(minimum, maximum, fallback, integer)
    local text = integer and string.format("%d", value) or formatNumber(value)
    if self.Box.Text ~= text then
        self.Box.Text = text
    end
    return value
end

function Field:OnChanged(callback)
    self.Box:GetPropertyChangedSignal("Text"):Connect(function()
        callback(self.Box.Text)
    end)
end

function Field:OnCommit(callback)
    self.Box.FocusLost:Connect(function(enterPressed)
        callback(self.Box.Text, enterPressed)
    end)
end

function Kit.field(parent, labelText, value, opts)
    opts = opts or {}
    local height = opts.height or 32
    local labelWidth = opts.labelWidth or 112

    local row = Instance.new("Frame")
    row.BackgroundTransparency = 1
    row.Size = UDim2.new(1, 0, 0, height)
    row.LayoutOrder = opts.order or 0
    row.Parent = parent

    local label = Kit.label(row, labelText, {
        size = 11.5,
        color = THEME.textDim,
        height = height,
    })
    label.Size = UDim2.new(0, labelWidth, 1, 0)
    label.Position = UDim2.new(0, 0, 0, 0)

    local inset = Instance.new("Frame")
    inset.BackgroundColor3 = THEME.inset
    inset.BorderSizePixel = 0
    inset.Size = UDim2.new(1, -(labelWidth + 10), 1, 0)
    inset.Position = UDim2.new(0, labelWidth + 10, 0, 0)
    inset.Parent = row
    Kit.round(inset, 8)
    local stroke = Kit.edge(inset, THEME.line, 0.25, 0.65)
    Kit.fill(inset, THEME.inputTop, THEME.inset)

    local box = Instance.new("TextBox")
    box.BackgroundTransparency = 1
    box.BorderSizePixel = 0
    box.Text = tostring(value == nil and "" or value)
    box.PlaceholderText = opts.placeholder or ""
    box.PlaceholderColor3 = THEME.textFaint
    box.TextColor3 = THEME.text
    box.Font = Enum.Font.Code
    box.TextSize = 12
    box.ClearTextOnFocus = false
    box.TextXAlignment = Enum.TextXAlignment.Left
    box.Position = UDim2.fromOffset(10, 0)
    box.Size = UDim2.new(1, -(opts.step and 42 or 20), 1, 0)
    box.Parent = inset

    local self = setmetatable({
        Row = row,
        Box = box,
        Label = label,
        Inset = inset,
        Stroke = stroke,
        min = opts.min,
        max = opts.max,
        step = opts.step,
        fallback = opts.fallback,
    }, Field)

    box.Focused:Connect(function()
        if stroke then
            stroke.Color = THEME.accent
            stroke.Transparency = 0
        end
    end)
    box.FocusLost:Connect(function()
        if stroke then
            stroke.Color = THEME.line
            stroke.Transparency = 0
        end
    end)

    if opts.step then
        local stepHost = Instance.new("Frame")
        stepHost.BackgroundTransparency = 1
        stepHost.AnchorPoint = Vector2.new(1, 0.5)
        stepHost.Position = UDim2.new(1, -4, 0.5, 0)
        stepHost.Size = UDim2.fromOffset(30, height - 8)
        stepHost.Parent = inset

        local divider = Instance.new("Frame")
        divider.BackgroundColor3 = THEME.lineSoft
        divider.BorderSizePixel = 0
        divider.Size = UDim2.new(0, 1, 1, -8)
        divider.Position = UDim2.new(0, -6, 0, 4)
        divider.Parent = stepHost

        local function stepperButton(glyph, delta, positionY)
            local button = Instance.new("TextButton")
            button.BackgroundColor3 = THEME.raised
            button.BackgroundTransparency = 0.35
            button.BorderSizePixel = 0
            button.AutoButtonColor = false
            button.Text = glyph
            button.TextColor3 = THEME.textDim
            button.TextSize = 11
            button.Font = Enum.Font.GothamBold
            button.Position = UDim2.new(0, 0, 0, positionY)
            button.Size = UDim2.new(1, 0, 0.5, -1)
            button.Parent = stepHost
            Kit.round(button, 4)
            button.MouseEnter:Connect(function()
                safeTween(button, { BackgroundColor3 = THEME.hover, TextColor3 = THEME.accent }, 0.1)
            end)
            button.MouseLeave:Connect(function()
                safeTween(button, { BackgroundColor3 = THEME.raised, TextColor3 = THEME.textDim }, 0.1)
            end)
            button.MouseButton1Click:Connect(function()
                local current = self:Number(self.min, self.max, self.fallback)
                local nextValue = current + delta
                local text
                if self.step and self.step >= 1 then
                    text = string.format("%d", math.floor(nextValue))
                else
                    text = formatNumber(nextValue)
                end
                self:SetText(text)
                self:Commit(self.min, self.max, self.fallback)
            end)
        end

        stepperButton("−", -(opts.step), 0)
        stepperButton("+", opts.step, height / 2 - 4)
    end

    return self
end

local Triple = {}
Triple.__index = Triple

function Triple:Numbers(minimum, maximum, fallback)
    local values = {}
    for index = 1, 3 do
        values[index] = self.Fields[index]:Number(minimum, maximum, fallback or 0)
    end
    return values[1], values[2], values[3]
end

function Triple:Commit(minimum, maximum, fallback)
    for index = 1, 3 do
        self.Fields[index]:Commit(minimum, maximum, fallback or 0)
    end
end

function Triple:SetTexts(a, b, c)
    self.Fields[1].Box.Text = tostring(a)
    self.Fields[2].Box.Text = tostring(b)
    self.Fields[3].Box.Text = tostring(c)
end

function Triple:OnChanged(callback)
    for _, field in ipairs(self.Fields) do
        field.Box:GetPropertyChangedSignal("Text"):Connect(callback)
    end
end

function Triple:OnCommit(callback)
    for _, field in ipairs(self.Fields) do
        field.Box.FocusLost:Connect(function()
            callback()
        end)
    end
end

function Kit.triple(parent, labelText, values, opts)
    opts = opts or {}
    local height = opts.height or 32
    local labelWidth = opts.labelWidth or 112
    local gap = 8

    local row = Instance.new("Frame")
    row.BackgroundTransparency = 1
    row.Size = UDim2.new(1, 0, 0, height)
    row.LayoutOrder = opts.order or 0
    row.Parent = parent

    local label = Kit.label(row, labelText, { size = 11.5, color = THEME.textDim, height = height })
    label.Size = UDim2.new(0, labelWidth, 1, 0)
    label.Position = UDim2.new(0, 0, 0, 0)

    local host = Instance.new("Frame")
    host.BackgroundTransparency = 1
    host.Size = UDim2.new(1, -(labelWidth + 10), 1, 0)
    host.Position = UDim2.new(0, labelWidth + 10, 0, 0)
    host.Parent = row
    Kit.hlist(host, gap)

    local axisColors = {
        opts.axes and opts.axes[1] or THEME.axisX,
        opts.axes and opts.axes[2] or THEME.axisY,
        opts.axes and opts.axes[3] or THEME.axisZ,
    }
    local axisNames = { "X", "Y", "Z" }

    local fields = {}
    for index = 1, 3 do
        local inset = Instance.new("Frame")
        inset.BackgroundColor3 = THEME.inset
        inset.BorderSizePixel = 0
        inset.Size = UDim2.new(1 / 3, -(gap * 2) / 3, 1, 0)
        inset.LayoutOrder = index
        inset.Parent = host
        Kit.round(inset, 8)
        Kit.edge(inset, THEME.line, 0.25, 0.65)
        Kit.fill(inset, THEME.inputTop, THEME.inset)

        local tick = Instance.new("Frame")
        tick.BackgroundColor3 = axisColors[index]
        tick.BorderSizePixel = 0
        tick.Size = UDim2.new(0, 2, 1, -14)
        tick.Position = UDim2.new(0, 5, 0, 7)
        tick.Parent = inset
        Kit.round(tick, 1)

        local box = Instance.new("TextBox")
        box.BackgroundTransparency = 1
        box.BorderSizePixel = 0
        box.Text = tostring(values and values[index] or "")
        box.PlaceholderText = axisNames[index]
        box.PlaceholderColor3 = axisColors[index]
        box.TextColor3 = THEME.text
        box.Font = Enum.Font.Code
        box.TextSize = 12
        box.ClearTextOnFocus = false
        box.TextXAlignment = Enum.TextXAlignment.Center
        box.Size = UDim2.new(1, -12, 1, 0)
        box.Position = UDim2.fromOffset(8, 0)
        box.Parent = inset

        fields[index] = setmetatable({ Row = row, Box = box, Inset = inset }, Field)

        local stroke = inset:FindFirstChildOfClass("UIStroke")
        box.Focused:Connect(function()
            if stroke then
                stroke.Color = axisColors[index]
                stroke.Transparency = 0
            end
            box.PlaceholderColor3 = THEME.textFaint
        end)
        box.FocusLost:Connect(function()
            if stroke then
                stroke.Color = THEME.line
                stroke.Transparency = 0.25
            end
            box.PlaceholderColor3 = axisColors[index]
        end)
    end

    return setmetatable({ Row = row, Fields = fields, Label = label }, Triple)
end

local Toggle = {}
Toggle.__index = Toggle

function Toggle:Value()
    return self.state
end

function Toggle:Set(value)
    self.state = value and true or false
    self:Refresh(true)
end

function Toggle:Refresh(animated)
    local on = self.state
    local time = animated and 0.18 or 0.01
    safeTween(self.Knob, {
        Position = UDim2.new(0, on and 18 or 3, 0.5, 0),
        BackgroundColor3 = THEME.white,
    }, time, Enum.EasingStyle.Quart)
    safeTween(self.Track, {
        BackgroundColor3 = on and THEME.accent or Color3.fromRGB(226, 226, 231),
    }, time)
    if self.TrackFill then
        safeTween(self.TrackFill, {
            BackgroundTransparency = on and 0 or 1,
        }, time)
    end
    safeTween(self.Label, {
        TextColor3 = on and THEME.text or THEME.textDim,
    }, time)
    self.State.Text = on and "ON" or "OFF"
    self.State.TextColor3 = on and THEME.accent or THEME.textFaint
end

function Toggle:OnChange(callback)
    self.callback = callback
end

function Kit.toggle(parent, text, initialValue, opts)
    opts = opts or {}
    local height = opts.height or 34
    local row = Instance.new("Frame")
    row.BackgroundColor3 = THEME.raised
    row.BackgroundTransparency = 0.1
    row.BorderSizePixel = 0
    row.Size = UDim2.new(1, 0, 0, height)
    row.LayoutOrder = opts.order or 0
    row.ClipsDescendants = true
    row.Parent = parent
    Kit.round(row, 9)
    local stroke = Kit.edge(row, THEME.line, 0.3, 0.75)

    local label = Kit.label(row, text, { size = 11.5, color = THEME.textDim })
    label.Position = UDim2.fromOffset(12, 0)
    label.Size = UDim2.new(1, -100, 1, 0)

    local stateLabel = Kit.label(row, "OFF", { size = 9.5, color = THEME.textFaint, bold = true })
    stateLabel.AnchorPoint = Vector2.new(1, 0.5)
    stateLabel.Position = UDim2.new(1, -46, 0.5, 0)
    stateLabel.Size = UDim2.fromOffset(28, 14)
    stateLabel.TextXAlignment = Enum.TextXAlignment.Right
    stateLabel.Font = Enum.Font.Code

    local track = Instance.new("Frame")
    track.BackgroundColor3 = THEME.inset
    track.BorderSizePixel = 0
    track.AnchorPoint = Vector2.new(1, 0.5)
    track.Position = UDim2.new(1, -10, 0.5, 0)
    track.Size = UDim2.fromOffset(34, 18)
    track.Parent = row
    Kit.round(track, 9)
    Kit.outline(track, THEME.line, 1, 0.5)

    local trackFill = Instance.new("Frame")
    trackFill.BackgroundColor3 = THEME.accent
    trackFill.BorderSizePixel = 0
    trackFill.Size = UDim2.fromScale(1, 1)
    trackFill.BackgroundTransparency = 1
    trackFill.Parent = track
    Kit.round(trackFill, 9)
    Kit.fill(trackFill, THEME.accentAlt, THEME.accent, 0)

    local knob = Instance.new("Frame")
    knob.BackgroundColor3 = THEME.textFaint
    knob.BorderSizePixel = 0
    knob.AnchorPoint = Vector2.new(0, 0.5)
    knob.Position = UDim2.new(0, 3, 0.5, 0)
    knob.Size = UDim2.fromOffset(12, 12)
    knob.Parent = track
    Kit.round(knob, 6)
    Kit.outline(knob, Color3.fromRGB(150, 150, 158), 1, 0.55)

    local hit = Instance.new("TextButton")
    hit.BackgroundTransparency = 1
    hit.Text = ""
    hit.AutoButtonColor = false
    hit.Size = UDim2.new(1, 0, 1, 0)
    hit.Parent = row

    local self = setmetatable({
        Instance = row,
        Stroke = stroke,
        Label = label,
        State = stateLabel,
        Track = track,
        TrackFill = trackFill,
        Knob = knob,
        state = initialValue and true or false,
    }, Toggle)
    self:Refresh(false)

    hit.MouseButton1Click:Connect(function()
        self.state = not self.state
        self:Refresh(true)
        if self.callback then
            local ok, err = pcall(self.callback, self.state)
            if not ok then
                App.fail(text or "开关", err)
            end
        end
    end)

    return self
end

local Rail = {}
Rail.__index = Rail

function Rail:Select(index)
    index = clamp(index, 1, #self.Buttons)
    if self.Active == index then
        return
    end
    self.Active = index
    for position, item in ipairs(self.Buttons) do
        local active = (position == index)
        safeTween(item.Instance, {
            BackgroundColor3 = active and THEME.surface or THEME.rail,
            BackgroundTransparency = active and 0 or 1,
        }, CONFIG.ANIM)
        safeTween(item.Instance, {
            TextColor3 = active and THEME.accent or THEME.textDim,
        }, CONFIG.ANIM)
        safeTween(item.Dot, {
            BackgroundColor3 = active and THEME.accent or THEME.line,
            Size = UDim2.fromOffset(active and 6 or 4, active and 6 or 4),
        }, CONFIG.ANIM)
    end
    local targetY = self.Buttons[index].Instance.Position.Y.Offset
    safeTween(self.Indicator, {
        Position = UDim2.new(0, 0, 0, targetY + 11),
    }, 0.22, Enum.EasingStyle.Quint)
    if self.onSelect then
        local ok, err = pcall(self.onSelect, index)
        if not ok then
            App.fail("切换页面", err)
        end
    end
end

function Kit.rail(parent, items, onSelect)
    local rail = Instance.new("Frame")
    rail.Name = "Rail"
    rail.BackgroundColor3 = THEME.rail
    rail.BorderSizePixel = 0
    rail.Size = UDim2.new(0, CONFIG.RAIL_WIDTH, 1, 0)
    rail.Parent = parent
    Kit.round(rail, 16)

    local edgeLine = Instance.new("Frame")
    edgeLine.BackgroundColor3 = THEME.lineSoft
    edgeLine.BorderSizePixel = 0
    edgeLine.AnchorPoint = Vector2.new(1, 0)
    edgeLine.Position = UDim2.new(1, 0, 0, 0)
    edgeLine.Size = UDim2.new(0, 1, 1, 0)
    edgeLine.Parent = rail
    Kit.fill(edgeLine, THEME.line, THEME.rail, 90)

    local brand = Instance.new("Frame")
    brand.BackgroundTransparency = 1
    brand.Size = UDim2.new(1, 0, 0, 64)
    brand.Parent = rail

    local markHost = Instance.new("Frame")
    markHost.BackgroundTransparency = 1
    markHost.Position = UDim2.fromOffset(16, 20)
    markHost.Size = UDim2.fromOffset(24, 24)
    markHost.Parent = brand

    local markOuter = Instance.new("Frame")
    markOuter.BackgroundColor3 = THEME.accent
    markOuter.BorderSizePixel = 0
    markOuter.AnchorPoint = Vector2.new(0.5, 0.5)
    markOuter.Position = UDim2.fromScale(0.5, 0.5)
    markOuter.Size = UDim2.fromOffset(18, 18)
    markOuter.Rotation = 45
    markOuter.Parent = markHost
    Kit.round(markOuter, 5)
    Kit.fill(markOuter, THEME.accent, THEME.accentAlt, 45)

    local markInner = Instance.new("Frame")
    markInner.BackgroundColor3 = THEME.rail
    markInner.BorderSizePixel = 0
    markInner.AnchorPoint = Vector2.new(0.5, 0.5)
    markInner.Position = UDim2.fromScale(0.5, 0.5)
    markInner.Size = UDim2.fromOffset(7, 7)
    markInner.Rotation = 45
    markInner.Parent = markHost
    Kit.round(markInner, 2)

    local brandTitle = Kit.label(brand, "OBJ", { bold = true, size = 14 })
    brandTitle.Position = UDim2.fromOffset(50, 18)
    brandTitle.Size = UDim2.fromOffset(90, 16)

    local brandSub = Kit.label(brand, "WIREFRAME", { size = 8.5, color = THEME.textFaint })
    brandSub.Position = UDim2.fromOffset(50, 33)
    brandSub.Size = UDim2.fromOffset(90, 12)

    local signRule = Instance.new("Frame")
    signRule.BackgroundColor3 = THEME.textFaint
    signRule.BackgroundTransparency = 0.45
    signRule.BorderSizePixel = 0
    signRule.Position = UDim2.fromOffset(50, 54)
    signRule.Size = UDim2.fromOffset(12, 1)
    signRule.Parent = brand

    local brandSign = Kit.label(brand, "lyra", { size = 9, color = THEME.textFaint })
    brandSign.Position = UDim2.fromOffset(68, 48)
    brandSign.Size = UDim2.fromOffset(72, 12)

    local navHost = Instance.new("Frame")
    navHost.BackgroundTransparency = 1
    navHost.Position = UDim2.fromOffset(0, 70)
    navHost.Size = UDim2.new(1, 0, 1, -150)
    navHost.Parent = rail

    local indicator = Instance.new("Frame")
    indicator.BackgroundColor3 = THEME.accent
    indicator.BorderSizePixel = 0
    indicator.Position = UDim2.new(0, 0, 0, 11)
    indicator.Size = UDim2.fromOffset(3, 24)
    indicator.Parent = navHost
    Kit.round(indicator, 2)
    Kit.fill(indicator, THEME.accent, THEME.accentAlt, 90)

    local self = setmetatable({
        Instance = rail,
        Buttons = {},
        Indicator = indicator,
        Active = 0,
        onSelect = onSelect,
    }, Rail)

    local itemHeight = 46
    local itemGap = 4
    for index, label in ipairs(items) do
        local item = Instance.new("TextButton")
        item.BackgroundColor3 = THEME.rail
        item.BackgroundTransparency = 1
        item.BorderSizePixel = 0
        item.AutoButtonColor = false
        item.Text = label
        item.TextColor3 = THEME.textDim
        item.Font = Enum.Font.Gotham
        item.TextSize = 12
        item.TextXAlignment = Enum.TextXAlignment.Left
        item.TextTruncate = Enum.TextTruncate.AtEnd
        item.Position = UDim2.fromOffset(0, (index - 1) * (itemHeight + itemGap))
        item.Size = UDim2.new(1, 0, 0, itemHeight)
        item.Parent = navHost
        Kit.round(item, 8)
        Kit.padding(item, 0, 10, 0, 26)

        local dot = Instance.new("Frame")
        dot.BackgroundColor3 = THEME.line
        dot.BorderSizePixel = 0
        dot.AnchorPoint = Vector2.new(0.5, 0.5)
        dot.Position = UDim2.new(0, -13, 0.5, 0)
        dot.Size = UDim2.fromOffset(4, 4)
        dot.Parent = item
        Kit.round(dot, 2)

        item.MouseEnter:Connect(function()
            if self.Active ~= index then
                safeTween(item, {
                    BackgroundColor3 = THEME.hover,
                    BackgroundTransparency = 0,
                }, CONFIG.ANIM)
            end
        end)
        item.MouseLeave:Connect(function()
            if self.Active ~= index then
                safeTween(item, {
                    BackgroundColor3 = THEME.rail,
                    BackgroundTransparency = 1,
                }, CONFIG.ANIM)
            end
        end)
        item.MouseButton1Click:Connect(function()
            local ok, err = pcall(function()
                self:Select(index)
            end)
            if not ok then
                App.fail("切换页面", err)
            end
        end)

        self.Buttons[index] = { Instance = item, Dot = dot }
    end

    local footer = Instance.new("Frame")
    footer.BackgroundTransparency = 1
    footer.AnchorPoint = Vector2.new(0, 1)
    footer.Position = UDim2.new(0, 0, 1, -14)
    footer.Size = UDim2.new(1, 0, 0, 40)
    footer.Parent = rail

    local footerLine = Instance.new("Frame")
    footerLine.BackgroundColor3 = THEME.lineSoft
    footerLine.BorderSizePixel = 0
    footerLine.Position = UDim2.fromOffset(16, 0)
    footerLine.Size = UDim2.new(1, -32, 0, 1)
    footerLine.Parent = footer

    local version = Kit.label(footer, "CORE " .. tostring(Core.VERSION or "-"), {
        size = 8.5,
        color = THEME.textFaint,
    })
    version.Position = UDim2.fromOffset(16, 8)
    version.Size = UDim2.new(1, -32, 0, 12)
    version.Font = Enum.Font.Code

    local uiVersion = Kit.label(footer, "UI " .. CONFIG.UI_VERSION, {
        size = 8.5,
        color = THEME.textFaint,
    })
    uiVersion.Position = UDim2.fromOffset(16, 21)
    uiVersion.Size = UDim2.new(1, -32, 0, 12)
    uiVersion.Font = Enum.Font.Code

    return self
end

function Kit.statChip(parent, name, order)
    local chip = Instance.new("Frame")
    chip.BackgroundColor3 = THEME.inset
    chip.BackgroundTransparency = 0.25
    chip.BorderSizePixel = 0
    chip.Size = UDim2.new(0.25, -6, 0, 48)
    chip.LayoutOrder = order or 0
    chip.Parent = parent
    Kit.round(chip, 9)
    Kit.edge(chip, THEME.line, 0.3, 0.75)

    local value = Kit.label(chip, "0", { bold = true, size = 17, color = THEME.text })
    value.Position = UDim2.fromOffset(10, 6)
    value.Size = UDim2.new(1, -20, 0, 20)

    local caption = Kit.label(chip, name, { size = 9.5, color = THEME.textFaint })
    caption.Position = UDim2.fromOffset(10, 26)
    caption.Size = UDim2.new(1, -20, 0, 12)

    return { Frame = chip, Value = value, Caption = caption }
end

local Modal = {}
Modal.__index = Modal

function Modal:Open()
    self.Overlay.Visible = true
    self.Panel.Size = UDim2.new(self.restSize.X.Scale, self.restSize.X.Offset - 16,
        self.restSize.Y.Scale, self.restSize.Y.Offset - 12)
    self.Panel.BackgroundTransparency = 0.25
    safeTween(self.Overlay, { BackgroundTransparency = 0.45 }, 0.15)
    safeTween(self.Panel, {
        Size = self.restSize,
        BackgroundTransparency = 0.02,
    }, 0.2, Enum.EasingStyle.Quint)
end

function Modal:Close()
    safeTween(self.Overlay, { BackgroundTransparency = 1 }, 0.12)
    safeTween(self.Panel, {
        Size = UDim2.new(self.restSize.X.Scale, self.restSize.X.Offset - 12,
            self.restSize.Y.Scale, self.restSize.Y.Offset - 10),
        BackgroundTransparency = 0.3,
    }, 0.12)
    task.delay(0.13, function()
        pcall(function()
            self.Overlay.Visible = false
            self.Overlay.BackgroundTransparency = 0.45
        end)
    end)
end

function Kit.modal(container, name, titleText, maxWidth, maxHeight)
    local overlay = Instance.new("Frame")
    overlay.Name = name .. "Overlay"
    overlay.BackgroundColor3 = THEME.scrim
    overlay.BackgroundTransparency = 0.45
    overlay.BorderSizePixel = 0
    overlay.Size = UDim2.new(1, 0, 1, 0)
    overlay.Visible = false
    overlay.Active = true
    overlay.Parent = container

    local blocker = Instance.new("TextButton")
    blocker.BackgroundTransparency = 1
    blocker.Text = ""
    blocker.AutoButtonColor = false
    blocker.Size = UDim2.new(1, 0, 1, 0)
    blocker.ZIndex = 1
    blocker.Parent = overlay

    local panel = Instance.new("Frame")
    panel.Name = name
    panel.AnchorPoint = Vector2.new(0.5, 0.5)
    panel.Position = UDim2.new(0.5, 0, 0.5, 0)
    panel.Size = UDim2.new(0.9, 0, 0.84, 0)
    panel.BackgroundColor3 = THEME.surface
    panel.BorderSizePixel = 0
    panel.ClipsDescendants = true
    panel.ZIndex = 2
    panel.Parent = overlay
    Kit.round(panel, 14)
    Kit.edge(panel, THEME.line, 0.05, 0.6)
    Kit.fill(panel, THEME.cardTop, THEME.surface)

    local constraint = Instance.new("UISizeConstraint")
    constraint.MaxSize = Vector2.new(maxWidth or 760, maxHeight or 580)
    constraint.MinSize = Vector2.new(320, 260)
    constraint.Parent = panel

    local header = Instance.new("Frame")
    header.BackgroundTransparency = 1
    header.Size = UDim2.new(1, 0, 0, 46)
    header.Parent = panel

    local title = Kit.label(header, titleText, { bold = true, size = 13 })
    title.Position = UDim2.fromOffset(18, 0)
    title.Size = UDim2.new(1, -70, 1, 0)

    local close = Kit.button(header, "×", { tone = "quiet" })
    close.Instance.AnchorPoint = Vector2.new(1, 0.5)
    close.Instance.Position = UDim2.new(1, -14, 0.5, 0)
    close.Instance.Size = UDim2.fromOffset(28, 26)
    close:SetTextSize(15)

    local hairline = Instance.new("Frame")
    hairline.BackgroundColor3 = THEME.lineSoft
    hairline.BorderSizePixel = 0
    hairline.Position = UDim2.fromOffset(0, 46)
    hairline.Size = UDim2.new(1, 0, 0, 1)
    hairline.Parent = panel
    Kit.fill(hairline, THEME.line, THEME.lineSoft, 0)

    local body = Instance.new("Frame")
    body.Name = "Body"
    body.BackgroundTransparency = 1
    body.Position = UDim2.new(0, 0, 0, 47)
    body.Size = UDim2.new(1, 0, 1, -47)
    body.Parent = panel

    local self = setmetatable({
        Overlay = overlay,
        Panel = panel,
        Body = body,
        CloseButton = close,
        restSize = panel.Size,
    }, Modal)

    close:OnClick(function()
        self:Close()
    end)

    return self
end

local toastToken = 0

function App.status(text, kind)
    text = tostring(text or "")
    kind = kind or "info"

    local dotColor
    if kind == "error" then
        dotColor = Color3.fromRGB(0, 0, 0)
    elseif kind == "warn" then
        dotColor = Color3.fromRGB(44, 44, 50)
    elseif kind == "ok" then
        dotColor = Color3.fromRGB(138, 138, 146)
    else
        dotColor = Color3.fromRGB(109, 109, 118)
    end

    if UI.statusLabel then
        UI.statusLabel.Text = text
        UI.statusLabel.Font = (kind == "error") and Enum.Font.GothamBold or Enum.Font.Gotham
        if kind == "error" then
            UI.statusLabel.TextColor3 = Color3.fromRGB(0, 0, 0)
        elseif kind == "warn" then
            UI.statusLabel.TextColor3 = Color3.fromRGB(24, 24, 28)
        else
            UI.statusLabel.TextColor3 = THEME.textDim
        end
    end
    if UI.statusDot then
        UI.statusDot.BackgroundColor3 = dotColor
    end
    if UI.statusChipDot then
        UI.statusChipDot.BackgroundColor3 = dotColor
    end
    if UI.statusChip then
        UI.statusChip.Text = (kind == "ok" and "完成")
            or (kind == "warn" and "注意")
            or (kind == "error" and "错误")
            or "运行中"
        UI.statusChip.TextColor3 = (kind == "ok" and THEME.ok)
            or (kind == "warn" and THEME.warn)
            or (kind == "error" and THEME.err)
            or THEME.textDim
    end

    if kind ~= "info" then
        Log.add(text, kind)
    end
    if kind == "warn" or kind == "error" then
        warn("[OBJ Wireframe] " .. text)
        App.toast(text, kind)
    else
        print("[OBJ Wireframe] " .. text)
    end
end

function App.fail(label, err)
    State.parsing = false
    State.generating = false
    State.actualBuilding = false
    State.previewBuilding = false
    State.previewPending = false
    State.clearOnCancel = false
    State.cancelRequested = false
    App.setProgress(0)
    App.status(string.format("%s 出错：%s", tostring(label or "操作"), tostring(err)), "error")
end

function App.toast(text, kind)
    local frame = UI.toastFrame
    if not frame then
        return
    end
    toastToken = toastToken + 1
    local token = toastToken

    local color = (kind == "error" and Color3.fromRGB(0, 0, 0))
        or (kind == "warn" and Color3.fromRGB(58, 58, 66))
        or Color3.fromRGB(150, 150, 158)
    frame.BackgroundColor3 = THEME.surface
    UI.toastAccent.BackgroundColor3 = color
    UI.toastLabel.Text = shorten(text, 96)
    UI.toastLabel.Font = (kind == "error") and Enum.Font.GothamBold or Enum.Font.Gotham
    UI.toastLabel.TextColor3 = (kind == "error" and Color3.fromRGB(0, 0, 0))
        or THEME.text

    frame.Visible = true
    frame.Position = UDim2.new(0.5, 0, 1, -6)
    frame.BackgroundTransparency = 0.5
    safeTween(frame, {
        Position = UDim2.new(0.5, 0, 1, -18),
        BackgroundTransparency = 0.04,
    }, 0.22, Enum.EasingStyle.Quint)

    task.delay(CONFIG.TOAST_SECONDS, function()
        pcall(function()
            if toastToken ~= token or not frame.Visible then
                return
            end
            safeTween(frame, {
                Position = UDim2.new(0.5, 0, 1, -4),
                BackgroundTransparency = 1,
            }, 0.2)
            task.delay(0.22, function()
                pcall(function()
                    if toastToken == token then
                        frame.Visible = false
                    end
                end)
            end)
        end)
    end)
end

function App.setProgress(alpha)
    alpha = clamp(alpha or 0, 0, 1)
    if UI.progressFill then
        UI.progressFill.Size = UDim2.new(alpha, 0, 1, 0)
    end
    if UI.progressText then
        UI.progressText.Text = string.format("%d%%", math.floor(alpha * 100 + 0.5))
    end
end

for _, name in ipairs({ "OBJWireframeImporter", "OBJWireframeTools", "OBJWireframeOpen" }) do
    local existing = PlayerGui:FindFirstChild(name)
    if existing then
        pcall(function()
            existing:Destroy()
        end)
    end
end

local gui = Instance.new("ScreenGui")
gui.Name = "OBJWireframeImporter"
gui.ResetOnSpawn = false
gui.IgnoreGuiInset = false
gui.ZIndexBehavior = Enum.ZIndexBehavior.Sibling
gui.DisplayOrder = 20
gui.Parent = PlayerGui

local modalGui = Instance.new("ScreenGui")
modalGui.Name = "OBJWireframeTools"
modalGui.ResetOnSpawn = false
modalGui.ZIndexBehavior = Enum.ZIndexBehavior.Sibling
modalGui.DisplayOrder = 40
modalGui.Parent = PlayerGui

local shadow = Instance.new("Frame")
shadow.Name = "WindowShadow"
shadow.BackgroundColor3 = Color3.fromRGB(0, 0, 0)
shadow.BackgroundTransparency = 0.68
shadow.BorderSizePixel = 0
shadow.Position = UDim2.new(0, 54, 0, 80)
shadow.Size = UDim2.fromOffset(CONFIG.WINDOW_SIZE.X + 16, CONFIG.WINDOW_SIZE.Y + 16)
shadow.ZIndex = 1
shadow.Parent = gui
Kit.round(shadow, 22)

local shadowFar = Instance.new("Frame")
shadowFar.Name = "WindowShadowFar"
shadowFar.BackgroundColor3 = Color3.fromRGB(0, 0, 0)
shadowFar.BackgroundTransparency = 0.85
shadowFar.BorderSizePixel = 0
shadowFar.Position = UDim2.new(0, 46, 0, 72)
shadowFar.Size = UDim2.fromOffset(CONFIG.WINDOW_SIZE.X + 32, CONFIG.WINDOW_SIZE.Y + 32)
shadowFar.ZIndex = 1
shadowFar.Parent = gui
Kit.round(shadowFar, 30)

local window = Instance.new("Frame")
window.Name = "Window"
window.AnchorPoint = Vector2.new(0, 0)
window.Position = UDim2.new(0, 62, 0, 88)
window.Size = UDim2.fromOffset(CONFIG.WINDOW_SIZE.X, CONFIG.WINDOW_SIZE.Y)
window.BackgroundColor3 = THEME.base
window.BackgroundTransparency = 0.02
window.BorderSizePixel = 0
window.ClipsDescendants = true
window.Active = true
window.ZIndex = 2
window.Parent = gui
Kit.round(window, 16)
Kit.edge(window, THEME.line, 0.02, 0.55)

local uiScale = Instance.new("UIScale")
uiScale.Scale = 1
uiScale.Parent = window

window.Size = UDim2.fromOffset(CONFIG.WINDOW_SIZE.X - 18, CONFIG.WINDOW_SIZE.Y - 14)
window.BackgroundTransparency = 0.4
safeTween(window, {
    Size = UDim2.fromOffset(CONFIG.WINDOW_SIZE.X, CONFIG.WINDOW_SIZE.Y),
    BackgroundTransparency = 0.02,
}, 0.3, Enum.EasingStyle.Quint)

local PAGE_META = {
    { name = "导入", title = "导入模型", desc = "读取执行器工作区、粘贴文本，或自动查找 .obj" },
    { name = "变换", title = "几何变换", desc = "缩放、旋转、世界位置与锚点" },
    { name = "生成", title = "生成线框", desc = "本地 Part 线框：不消耗库存，只有自己看得见" },
    { name = "建造", title = "预览与建造", desc = "本机预览；或用游戏内工具在服务器上实际建造" },
    { name = "外壳", title = "体素外壳", desc = "全模型共享世界体素格，铺出完整表面壳" },
}

local pages = {}

local tabBar = Kit.rail(window, { "导入", "变换", "生成", "建造", "外壳" }, function(index)
    for position, page in ipairs(pages) do
        page.Visible = (position == index)
    end
    State.activeTab = index
    local meta = PAGE_META[index]
    if meta and UI.pageTitle then
        UI.pageTitle.Text = meta.title
        UI.pageSubtitle.Text = meta.desc
    end
end)

local main = Instance.new("Frame")
main.Name = "Main"
main.BackgroundTransparency = 1
main.Position = UDim2.new(0, CONFIG.RAIL_WIDTH, 0, 0)
main.Size = UDim2.new(1, -CONFIG.RAIL_WIDTH, 1, 0)
main.ZIndex = 2
main.Parent = window

local header = Instance.new("Frame")
header.Name = "Header"
header.BackgroundTransparency = 1
header.Size = UDim2.new(1, 0, 0, CONFIG.HEADER_HEIGHT)
header.Parent = main

local titleLabel = Kit.label(header, "导入模型", { bold = true, size = 16 })
titleLabel.Position = UDim2.fromOffset(22, 10)
titleLabel.Size = UDim2.new(1, -246, 0, 22)
UI.pageTitle = titleLabel

local subtitleLabel = Kit.label(header, PAGE_META[1].desc, { size = 11, color = THEME.textDim })
subtitleLabel.Position = UDim2.fromOffset(22, 33)
subtitleLabel.Size = UDim2.new(1, -246, 0, 16)
UI.pageSubtitle = subtitleLabel

local headerRight = Instance.new("Frame")
headerRight.Name = "HeaderControls"
headerRight.BackgroundTransparency = 1
headerRight.AnchorPoint = Vector2.new(1, 0)
headerRight.Position = UDim2.new(1, -14, 0, 16)
headerRight.Size = UDim2.fromOffset(188, 26)
headerRight.ZIndex = 8
headerRight.Parent = window

local statusChip = Instance.new("Frame")
statusChip.Name = "StatusChip"
statusChip.BackgroundColor3 = THEME.inset
statusChip.BorderSizePixel = 0
statusChip.Position = UDim2.fromOffset(0, 2)
statusChip.Size = UDim2.fromOffset(68, 22)
statusChip.ZIndex = 9
statusChip.Parent = headerRight
Kit.round(statusChip, 11)
Kit.outline(statusChip, THEME.lineSoft, 1, 0.25)

local statusChipDot = Instance.new("Frame")
statusChipDot.BackgroundColor3 = THEME.accent
statusChipDot.BorderSizePixel = 0
statusChipDot.AnchorPoint = Vector2.new(0, 0.5)
statusChipDot.Position = UDim2.new(0, 9, 0.5, 0)
statusChipDot.Size = UDim2.fromOffset(5, 5)
statusChipDot.ZIndex = 10
statusChipDot.Parent = statusChip
Kit.round(statusChipDot, 3)

local statusChipLabel = Kit.label(statusChip, "就绪", { size = 9.5, color = THEME.textDim })
statusChipLabel.Position = UDim2.fromOffset(19, 0)
statusChipLabel.Size = UDim2.new(1, -24, 1, 0)
statusChipLabel.ZIndex = 10
UI.statusChip = statusChipLabel
UI.statusChipDot = statusChipDot

function Kit.controlChip(parent, text, opts)
    opts = opts or {}

    local root = Instance.new("Frame")
    root.Name = opts.name or "Control"
    root.BackgroundColor3 = THEME.surface
    root.BorderSizePixel = 0
    root.Position = opts.position or UDim2.fromOffset(0, 0)
    root.Size = UDim2.fromOffset(opts.width or 28, opts.height or 26)
    root.ZIndex = opts.zindex or 9
    root.Parent = parent
    Kit.round(root, 8)
    Kit.outline(root, THEME.line, 1, 0.25)

    local label = Instance.new("TextLabel")
    label.Name = "Label"
    label.BackgroundTransparency = 1
    label.BorderSizePixel = 0
    label.Size = UDim2.fromScale(1, 1)
    label.Text = tostring(text or "")
    label.TextColor3 = THEME.text
    label.Font = Enum.Font.Gotham
    label.TextSize = opts.size or 11
    label.TextWrapped = false
    label.ZIndex = root.ZIndex + 1
    label.Parent = root

    local hit = Instance.new("TextButton")
    hit.Name = "Hit"
    hit.BackgroundTransparency = 1
    hit.Text = ""
    hit.AutoButtonColor = false
    hit.Size = UDim2.fromScale(1, 1)
    hit.ZIndex = root.ZIndex + 2
    hit.Parent = root

    local self = {
        Instance = root,
        Label = label,
        Hit = hit,
    }

    function self:SetText(value)
        self.Label.Text = tostring(value or "")
    end

    function self:GetText()
        return self.Label.Text
    end

    function self:OnClick(callback)
        self.Hit.MouseButton1Click:Connect(function()
            local ok, err = pcall(callback)
            if not ok then
                App.fail(self:GetText(), err)
            end
        end)
    end

    function self:SetNormal()
        self.Instance.BackgroundColor3 = THEME.surface
    end

    hit.MouseEnter:Connect(function()
        safeTween(root, { BackgroundColor3 = THEME.hover }, 0.1)
    end)
    hit.MouseLeave:Connect(function()
        safeTween(root, { BackgroundColor3 = THEME.surface }, 0.1)
    end)

    return self
end

local logButton = Kit.controlChip(headerRight, "日志", {
    name = "LogControl",
    width = 42,
    height = 26,
    size = 11,
    position = UDim2.fromOffset(76, 0),
})

local minimizeButton = Kit.controlChip(headerRight, "—", {
    name = "MinimizeControl",
    width = 28,
    height = 26,
    size = 14,
    position = UDim2.fromOffset(122, 0),
})

local closeButton = Kit.controlChip(headerRight, "×", {
    name = "CloseControl",
    width = 28,
    height = 26,
    size = 15,
    position = UDim2.fromOffset(152, 0),
})

pcall(function()
    local function hex(color)
        if not color then
            return "nil"
        end
        return string.format("#%02X%02X%02X",
            math.floor(color.R * 255 + 0.5),
            math.floor(color.G * 255 + 0.5),
            math.floor(color.B * 255 + 0.5))
    end

    local function peek(fn)
        local ok, value = pcall(fn)
        if ok then
            return value
        end
        return nil
    end

    local report = {}
    for _, control in ipairs({ logButton, minimizeButton, closeButton }) do
        local label = control.Label
        local size = peek(function()
            return label.AbsoluteSize
        end)
        local pos = peek(function()
            return label.AbsolutePosition
        end)
        report[#report + 1] = string.format(
            "[%s] 文字='%s' 颜色=%s 透明度=%.2f 尺寸=%sx%s 位置=%s,%s 底色=%s",
            control:GetText(),
            tostring(label.Text),
            hex(label.TextColor3),
            label.TextTransparency or 0,
            tostring(size and size.X),
            tostring(size and size.Y),
            tostring(pos and pos.X),
            tostring(pos and pos.Y),
            hex(control.Instance.BackgroundColor3)
        )
    end
    Log.add("页头控件自检 " .. table.concat(report, " · "), "info")
end)

function App.resetHeaderControls()
    for _, control in ipairs({ logButton, minimizeButton, closeButton }) do
        pcall(function()
            control:SetNormal()
        end)
    end
end

local dragSurface = Instance.new("TextButton")
dragSurface.Name = "DragSurface"
dragSurface.BackgroundTransparency = 1
dragSurface.Text = ""
dragSurface.AutoButtonColor = false
dragSurface.Position = UDim2.fromOffset(0, 0)
dragSurface.Size = UDim2.new(1, -206, 0, CONFIG.HEADER_HEIGHT)
dragSurface.ZIndex = 6
dragSurface.Parent = window

local headerLine = Instance.new("Frame")
headerLine.BackgroundColor3 = THEME.lineSoft
headerLine.BorderSizePixel = 0
headerLine.AnchorPoint = Vector2.new(0, 1)
headerLine.Position = UDim2.new(0, 0, 1, 0)
headerLine.Size = UDim2.new(1, 0, 0, 1)
headerLine.Parent = header
Kit.fill(headerLine, THEME.line, THEME.lineSoft, 0)

local content = Instance.new("Frame")
content.Name = "Content"
content.BackgroundTransparency = 1
content.Position = UDim2.new(0, 0, 0, CONFIG.HEADER_HEIGHT)
content.Size = UDim2.new(1, 0, 1, -(CONFIG.HEADER_HEIGHT + CONFIG.STATUS_HEIGHT))
content.ClipsDescendants = true
content.Parent = main

local statusBar = Instance.new("Frame")
statusBar.Name = "StatusBar"
statusBar.BackgroundColor3 = THEME.base
statusBar.BackgroundTransparency = 0
statusBar.BorderSizePixel = 0
statusBar.AnchorPoint = Vector2.new(0, 1)
statusBar.Position = UDim2.new(0, 0, 1, 0)
statusBar.Size = UDim2.new(1, 0, 0, CONFIG.STATUS_HEIGHT)
statusBar.Parent = main
Kit.round(statusBar, 16)

local statusTopLine = Instance.new("Frame")
statusTopLine.BackgroundColor3 = THEME.lineSoft
statusTopLine.BorderSizePixel = 0
statusTopLine.Size = UDim2.new(1, 0, 0, 1)
statusTopLine.Parent = statusBar

local progressTrack = Instance.new("Frame")
progressTrack.BackgroundColor3 = Color3.fromRGB(222, 222, 227)
progressTrack.BorderSizePixel = 0
progressTrack.Position = UDim2.new(0, 16, 0, 0)
progressTrack.Size = UDim2.new(1, -32, 0, 3)
progressTrack.Parent = statusBar
Kit.round(progressTrack, 2)

local progressFill = Instance.new("Frame")
progressFill.BackgroundColor3 = THEME.accent
progressFill.BorderSizePixel = 0
progressFill.Size = UDim2.new(0, 0, 1, 0)
progressFill.Parent = progressTrack
Kit.fill(progressFill, THEME.accent, THEME.accentAlt, 0)

local statusDot = Instance.new("Frame")
statusDot.BackgroundColor3 = THEME.accent
statusDot.BorderSizePixel = 0
statusDot.Position = UDim2.fromOffset(18, 22)
statusDot.Size = UDim2.fromOffset(6, 6)
statusDot.Parent = statusBar
Kit.round(statusDot, 3)

local statusLabel = Kit.label(statusBar, "就绪。", {
    wrap = true,
    size = 11,
    valign = Enum.TextYAlignment.Top,
})
statusLabel.AutomaticSize = Enum.AutomaticSize.None
statusLabel.Position = UDim2.fromOffset(32, 12)
statusLabel.Size = UDim2.new(1, -110, 0, 44)
UI.statusLabel = statusLabel

local progressText = Kit.label(statusBar, "0%", { size = 11, color = THEME.textFaint })
progressText.AnchorPoint = Vector2.new(1, 0)
progressText.Position = UDim2.new(1, -16, 0, 12)
progressText.Size = UDim2.fromOffset(58, 16)
progressText.TextXAlignment = Enum.TextXAlignment.Right
progressText.Font = Enum.Font.Code
UI.progressText = progressText
UI.progressFill = progressFill
UI.statusDot = statusDot

local resizeHandle = Instance.new("TextButton")
resizeHandle.Name = "ResizeHandle"
resizeHandle.BackgroundTransparency = 1
resizeHandle.Text = "◢"
resizeHandle.TextColor3 = THEME.textFaint
resizeHandle.TextSize = 12
resizeHandle.Font = Enum.Font.GothamBold
resizeHandle.AnchorPoint = Vector2.new(1, 1)
resizeHandle.Position = UDim2.new(1, -2, 1, -2)
resizeHandle.Size = UDim2.fromOffset(18, 18)
resizeHandle.AutoButtonColor = false
resizeHandle.ZIndex = 3
resizeHandle.Parent = statusBar

local openButton = Instance.new("TextButton")
openButton.Name = "OBJWireframeOpen"
openButton.BackgroundColor3 = THEME.accent
openButton.BorderSizePixel = 0
openButton.Text = "OBJ 线框"
openButton.TextColor3 = THEME.accentText
openButton.Font = Enum.Font.GothamBold
openButton.TextSize = 12
openButton.AutoButtonColor = false
openButton.Size = UDim2.fromOffset(98, 32)
openButton.Position = UDim2.new(0, 18, 1, -58)
openButton.Visible = false
openButton.ZIndex = 4
openButton.Parent = gui
Kit.round(openButton, 16)

local openShadow = Instance.new("Frame")
openShadow.BackgroundColor3 = Color3.fromRGB(0, 0, 0)
openShadow.BackgroundTransparency = 0.6
openShadow.BorderSizePixel = 0
openShadow.Size = UDim2.new(1, 8, 1, 8)
openShadow.Position = UDim2.fromOffset(-4, -4)
openShadow.ZIndex = 3
openShadow.Visible = false
openShadow.Parent = openButton
Kit.round(openShadow, 20)

openButton.MouseEnter:Connect(function()
    safeTween(openButton, { BackgroundTransparency = 0.12 }, 0.12)
end)
openButton.MouseLeave:Connect(function()
    safeTween(openButton, { BackgroundTransparency = 0 }, 0.12)
end)

local toastFrame = Instance.new("Frame")
toastFrame.Name = "Toast"
toastFrame.BackgroundColor3 = THEME.surface
toastFrame.BorderSizePixel = 0
toastFrame.AnchorPoint = Vector2.new(0.5, 1)
toastFrame.Position = UDim2.new(0.5, 0, 1, -18)
toastFrame.Size = UDim2.fromOffset(380, 38)
toastFrame.Visible = false
toastFrame.ZIndex = 6
toastFrame.Parent = gui
Kit.round(toastFrame, 10)
Kit.edge(toastFrame, THEME.line, 0.15, 0.6)

local toastAccent = Instance.new("Frame")
toastAccent.BackgroundColor3 = THEME.accent
toastAccent.BorderSizePixel = 0
toastAccent.Size = UDim2.new(0, 3, 1, -14)
toastAccent.Position = UDim2.fromOffset(0, 7)
toastAccent.ZIndex = 7
toastAccent.Parent = toastFrame
Kit.round(toastAccent, 2)

local toastLabel = Kit.label(toastFrame, "", { wrap = false, size = 11 })
toastLabel.Position = UDim2.fromOffset(14, 0)
toastLabel.Size = UDim2.new(1, -26, 1, 0)
toastLabel.ZIndex = 7
UI.toastFrame = toastFrame
UI.toastAccent = toastAccent
UI.toastLabel = toastLabel

local function newPage(index, name)
    local page = Instance.new("ScrollingFrame")
    page.Name = "Page_" .. name
    page.BackgroundTransparency = 1
    page.BorderSizePixel = 0
    page.Size = UDim2.new(1, 0, 1, 0)
    page.ScrollBarThickness = 4
    page.ScrollBarImageColor3 = THEME.line
    page.ScrollBarImageTransparency = 0.2
    page.ScrollingDirection = Enum.ScrollingDirection.Y
    page.CanvasSize = UDim2.new(0, 0, 0, 0)
    page.AutomaticCanvasSize = Enum.AutomaticSize.Y
    page.ElasticBehavior = Enum.ElasticBehavior.WhenScrollable
    page.Visible = (index == 1)
    page.ClipsDescendants = true
    page.Parent = content
    Kit.padding(page, 12, 12, 16, 14)
    Kit.vlist(page, 10)
    pages[index] = page
    return page
end

local importPage = newPage(1, "Import")

local envCard = Kit.card(importPage, "运行环境", 1, { index = 1 })
local capabilityLabel = Kit.label(envCard, "检测中 ...", {
    wrap = true,
    size = 11,
    color = THEME.textDim,
    valign = Enum.TextYAlignment.Top,
    order = 1,
})
UI.capabilityLabel = capabilityLabel

local envRow, envButtons = Kit.buttonRow(envCard, {
    {
        text = "重新检测环境",
        tone = "quiet",
        onClick = function()
            App.refreshCapabilities()
            App.refreshToolStatus()
            App.status("已重新检测执行器能力与建造工具。", "ok")
        end,
    },
}, { order = 2, height = 30 })
UI.redetectButton = envButtons[1]

local sourceCard = Kit.card(importPage, "导入来源", 2, { index = 2 })

local pathField = Kit.field(sourceCard, "工作区路径", "", {
    order = 1,
    labelWidth = 82,
    placeholder = "models/car.obj",
})
UI.pathField = pathField

local importRow, importButtons = Kit.buttonRow(sourceCard, {
    {
        text = "浏览",
        tone = "quiet",
        onClick = function()
            App.openBrowser()
        end,
    },
    {
        text = "读取解析",
        accent = true,
        onClick = function()
            App.importFromPath()
        end,
    },
    {
        text = "粘贴 OBJ",
        tone = "quiet",
        onClick = function()
            App.openPaste()
        end,
    },
    {
        text = "重新解析",
        tone = "quiet",
        onClick = function()
            App.reparse()
        end,
    },
}, { order = 2 })
UI.browseButton = importButtons[1]
UI.readButton = importButtons[2]
UI.pasteButton = importButtons[3]
UI.reparseButton = importButtons[4]

local findRow, findButtons = Kit.buttonRow(sourceCard, {
    {
        text = "自动查找 .obj",
        tone = "quiet",
        onClick = function()
            App.autoFindObj()
        end,
    },
    {
        text = "清空路径",
        tone = "ghost",
        onClick = function()
            UI.pathField:SetText("")
            App.status("已清空路径输入。", "info")
        end,
    },
}, { order = 3, height = 30 })
UI.autoFindButton = findButtons[1]

Kit.hint(
    sourceCard,
    "路径是执行器工作区内的相对路径，带引号会自动去掉。"
        .. "没有 readfile 时用「粘贴 OBJ」；没有 listfiles 时「浏览」与「自动查找」不可用，手动输入路径即可。",
    4
)

local statsCard = Kit.card(importPage, "模型统计", 3, { index = 3 })

local sourceLabel = Kit.label(statsCard, "尚未导入模型", { size = 12, color = THEME.textDim, order = 1 })
UI.sourceLabel = sourceLabel

local chipsHost = Instance.new("Frame")
chipsHost.BackgroundTransparency = 1
chipsHost.Size = UDim2.new(1, 0, 0, 48)
chipsHost.LayoutOrder = 2
chipsHost.Parent = statsCard
Kit.hlist(chipsHost, 8)

local chipVertices = Kit.statChip(chipsHost, "顶点", 1)
local chipFaces = Kit.statChip(chipsHost, "面", 2)
local chipEdges = Kit.statChip(chipsHost, "唯一边", 3)
local chipTriangles = Kit.statChip(chipsHost, "三角形", 4)
UI.statValues = { chipVertices.Value, chipFaces.Value, chipEdges.Value, chipTriangles.Value }

local statsLabel = Kit.label(statsCard, "", { size = 11, color = THEME.textFaint, order = 3 })
statsLabel.Visible = false
statsLabel.Size = UDim2.new(1, 0, 0, 0)
UI.statsLabel = statsLabel

local warningLabel = Kit.label(statsCard, "导入后会在这里显示解析警告。", {
    wrap = true,
    size = 11,
    color = THEME.textFaint,
    valign = Enum.TextYAlignment.Top,
    order = 4,
})
UI.warningLabel = warningLabel

local transformPage = newPage(2, "Transform")

local geometryCard = Kit.card(transformPage, "几何变换", 1, { index = 1 })

UI.scaleField = Kit.field(geometryCard, "缩放比例", "1", {
    order = 1,
    placeholder = "1",
    step = 0.1,
    min = 0.000001,
    max = 100000,
    fallback = 1,
})

UI.rotationTriple = Kit.triple(geometryCard, "旋转 X/Y/Z (°)", { "0", "0", "0" }, { order = 2 })

UI.positionTriple = Kit.triple(geometryCard, "世界位置 X/Y/Z", { "0", "10", "0" }, { order = 3 })

UI.thicknessField = Kit.field(geometryCard, "线框粗细", tostring(CONFIG.DEFAULT_THICKNESS), {
    order = 4,
    placeholder = "0.08",
    step = 0.01,
    min = CONFIG.MIN_PART_SIZE,
    max = 5,
    fallback = CONFIG.DEFAULT_THICKNESS,
})

Kit.hint(
    geometryCard,
    "旋转顺序固定 X→Y→Z。世界位置指「锚点」在游戏里的坐标，不是包围盒中心；默认 (0, 10, 0)。"
        .. "数值框右侧的 − / + 可以按步长微调。",
    5
)

local pivotCard = Kit.card(transformPage, "定位锚点", 2, { index = 2 })

local pivotRow, pivotButtons = Kit.buttonRow(pivotCard, {
    {
        text = "包围盒中心",
        onClick = function()
            State.pivotMode = "center"
            App.refreshPivotUI()
            App.status("锚点：包围盒中心（默认）。", "info")
        end,
    },
    {
        text = "OBJ 原点",
        onClick = function()
            State.pivotMode = "origin"
            App.refreshPivotUI()
            App.status("锚点：OBJ 原点 (0,0,0)。", "info")
        end,
    },
    {
        text = "自定义",
        onClick = function()
            State.pivotMode = "custom"
            App.refreshPivotUI()
            App.status("锚点：自定义坐标，可在下方输入。", "info")
        end,
    },
}, { order = 1 })

local customPivotRow = Instance.new("Frame")
customPivotRow.Name = "CustomPivot"
customPivotRow.BackgroundTransparency = 1
customPivotRow.Size = UDim2.new(1, 0, 0, 32)
customPivotRow.LayoutOrder = 2
customPivotRow.Visible = false
customPivotRow.Parent = pivotCard

local customPivotTriple = Kit.triple(customPivotRow, "自定义坐标", { "0", "0", "0" }, {
    order = 1,
    labelWidth = 82,
})
UI.customPivotRow = customPivotRow
UI.customPivotTriple = customPivotTriple

UI.pivotButtons = {
    center = pivotButtons[1],
    origin = pivotButtons[2],
    custom = pivotButtons[3],
}

Kit.hint(
    pivotCard,
    "锚点决定「缩放」与「旋转」围绕哪个点发生，也决定世界位置落在模型的哪一处。"
        .. "选错锚点最典型的现象是：旋转后模型绕着一个很远的点甩出去。",
    3
)

local quickCard = Kit.card(transformPage, "快捷定位", 3, { index = 3 })

UI.targetSizeField = Kit.field(quickCard, "目标尺寸 (studs)", tostring(CONFIG.DEFAULT_TARGET_SIZE), {
    order = 1,
    step = 1,
    min = 1,
    max = CONFIG.MAX_PART_LENGTH,
    fallback = CONFIG.DEFAULT_TARGET_SIZE,
})

local quickRow, quickButtons = Kit.buttonRow(quickCard, {
    {
        text = "按目标尺寸适配",
        accent = true,
        onClick = function()
            App.applyFit()
        end,
    },
    {
        text = "放到视角前方",
        tone = "quiet",
        onClick = function()
            App.applyPlaceInFront()
        end,
    },
}, { order = 2 })
UI.fitButton = quickButtons[1]
UI.placeButton = quickButtons[2]

Kit.hint(
    quickCard,
    "「适配」只改缩放比例，让最大包围盒边长接近目标值；「放到视角前方」只改世界位置，"
        .. "沿相机视线往前推，不改变旋转。两者可以连续点。",
    3
)

local generatePage = newPage(3, "Generate")

local limitCard = Kit.card(generatePage, "简化与上限", 1, { index = 1 })

UI.maxEdgeField = Kit.field(limitCard, "最大边数", tostring(CONFIG.DEFAULT_MAX_EDGES), {
    order = 1,
    placeholder = "1 - " .. tostring(CONFIG.HARD_MAX_EDGES),
    step = 500,
    min = 1,
    max = CONFIG.HARD_MAX_EDGES,
    fallback = CONFIG.DEFAULT_MAX_EDGES,
})

UI.autoSimplifyToggle = Kit.toggle(limitCard, "超过上限时自动做网格简化", true, { order = 2 })
UI.triangulateToggle = Kit.toggle(limitCard, "多边形三角化（增加内部对角线）", false, { order = 3 })
UI.triangulateToggle:OnChange(function()
    if State.sourceText then
        State.needsReparse = true
        App.updateStats()
        App.status("三角化设置已更改；生成前会重新解析，或手动点「重新解析」。", "warn")
    end
end)

UI.borderToggle = Kit.toggle(limitCard, "只保留边框 / 特征边（去掉内部线）", false, { order = 4 })
UI.borderAngleField = Kit.field(
    limitCard,
    "边框角度阈值 (°)",
    tostring(CONFIG.DEFAULT_FEATURE_EDGE_ANGLE),
    {
        order = 5,
        labelWidth = 142,
        step = 5,
        min = CONFIG.MIN_FEATURE_EDGE_ANGLE,
        max = CONFIG.MAX_FEATURE_EDGE_ANGLE,
        fallback = CONFIG.DEFAULT_FEATURE_EDGE_ANGLE,
    }
)

local function requestFeatureReparse()
    if not State.sourceText then
        return
    end
    if State.parsing then
        State.needsReparse = true
        return
    end
    if State.generating or State.actualBuilding then
        State.needsReparse = true
        App.status("边框设置已更改；当前任务结束后会重新解析。", "warn")
        return
    end
    State.needsReparse = true
    task.defer(function()
        if State.sourceText and not State.parsing and not State.generating and not State.actualBuilding then
            App.reparse()
        end
    end)
end

UI.borderToggle:OnChange(function()
    requestFeatureReparse()
    App.updateStats()
    App.status(
        UI.borderToggle:Value()
            and "已开启边框模式：只保留开口边界与硬边，正在重新解析 ..."
            or "已关闭边框模式：恢复全部网格边，正在重新解析 ...",
        "info"
    )
end)

UI.borderAngleField:OnCommit(function()
    requestFeatureReparse()
    App.updateStats()
    App.status("边框角度阈值已更改，正在重新解析 ...", "info")
end)

local estimateLabel = Kit.label(limitCard, "预计积木：尚未导入模型", {
    wrap = true,
    size = 11,
    color = THEME.textFaint,
    valign = Enum.TextYAlignment.Top,
    order = 6,
})
UI.estimateLabel = estimateLabel

Kit.hint(
    limitCard,
    "边框模式只保留“开口边界”和夹角 ≥ 阈值的硬边，内部共面三角线会被去掉。"
        .. "35° 适合大多数车架/机械；想要更多细节就降低到 20–30°，想要更干净就提高到 50–70°。"
        .. "曲面很顺的模型可能几乎没有特征边，此时请降低阈值或关闭边框模式。",
    7
)

local runCard = Kit.card(generatePage, "执行", 2, { index = 2 })

local runRow, runButtons = Kit.buttonRow(runCard, {
    {
        text = "开始生成",
        accent = true,
        onClick = function()
            App.startGeneration()
        end,
    },
    {
        text = "取消",
        tone = "quiet",
        onClick = function()
            App.cancelAll()
        end,
    },
    {
        text = "清除线框",
        tone = "danger",
        onClick = function()
            App.clearWireframe()
        end,
    },
}, { order = 1 })
UI.generateButton = runButtons[1]
UI.cancelButton = runButtons[2]
UI.clearButton = runButtons[3]

Kit.hint(
    runCard,
    "「开始生成」在本机创建 Part 线框，每条唯一边一根，不消耗服务器库存，别人看不见。"
        .. "生成中可以点「取消」；「清除线框」只删本脚本创建的文件夹。",
    2
)

local pasteModal = Kit.modal(modalGui, "PasteModal", "粘贴 OBJ 文本", 780, 600)

local pasteHint = Kit.label(
    pasteModal.Body,
    "支持 v / f / v/vt/vn、负索引、三角形、四边形与任意多边形。适合没有 readfile 的执行器。",
    { wrap = true, size = 11, color = THEME.textFaint, valign = Enum.TextYAlignment.Top }
)
pasteHint.Position = UDim2.fromOffset(16, 12)
pasteHint.Size = UDim2.new(1, -32, 0, 26)

local pasteInset = Instance.new("Frame")
pasteInset.BackgroundColor3 = THEME.inset
pasteInset.BorderSizePixel = 0
pasteInset.Position = UDim2.fromOffset(16, 44)
pasteInset.Size = UDim2.new(1, -32, 1, -100)
pasteInset.Parent = pasteModal.Body
Kit.round(pasteInset, 10)
Kit.edge(pasteInset, THEME.line, 0.2, 0.65)
Kit.fill(pasteInset, THEME.inputTop, THEME.inset)

local pasteBox = Instance.new("TextBox")
pasteBox.BackgroundTransparency = 1
pasteBox.BorderSizePixel = 0
pasteBox.Text = ""
pasteBox.PlaceholderText = "在此粘贴 OBJ 文本（Ctrl+V）..."
pasteBox.PlaceholderColor3 = THEME.textFaint
pasteBox.TextColor3 = THEME.text
pasteBox.Font = Enum.Font.Code
pasteBox.TextSize = 11
pasteBox.ClearTextOnFocus = false
pasteBox.MultiLine = true
pasteBox.TextWrapped = true
pasteBox.TextXAlignment = Enum.TextXAlignment.Left
pasteBox.TextYAlignment = Enum.TextYAlignment.Top
pasteBox.Size = UDim2.new(1, -16, 1, -16)
pasteBox.Position = UDim2.fromOffset(8, 8)
pasteBox.Parent = pasteInset

local pasteRow, pasteButtons = Kit.buttonRow(pasteModal.Body, {
    {
        text = "解析文本",
        accent = true,
        onClick = function()
            local text = pasteBox.Text
            if text == "" then
                App.status("粘贴框是空的。", "error")
                return
            end
            pasteModal:Close()
            App.importFromText(text, "粘贴文本")
        end,
    },
    {
        text = "清空",
        tone = "quiet",
        onClick = function()
            pasteBox.Text = ""
            pasteBox:CaptureFocus()
        end,
    },
    {
        text = "取消",
        tone = "quiet",
        onClick = function()
            pasteModal:Close()
        end,
    },
}, { order = 0 })
pasteRow.Position = UDim2.new(0, 16, 1, -44)
pasteRow.Size = UDim2.new(1, -32, 0, 32)
UI.pasteParseButton = pasteButtons[1]

local browserModal = Kit.modal(modalGui, "BrowserModal", "选择执行器工作区文件", 800, 620)

local browserPathLabel = Kit.label(browserModal.Body, "/", { size = 11, color = THEME.textDim })
browserPathLabel.Position = UDim2.fromOffset(16, 12)
browserPathLabel.Size = UDim2.new(1, -32, 0, 18)
browserPathLabel.Font = Enum.Font.Code

local browserList = Instance.new("ScrollingFrame")
browserList.Name = "FileList"
browserList.BackgroundColor3 = THEME.inset
browserList.BackgroundTransparency = 0.2
browserList.BorderSizePixel = 0
browserList.Position = UDim2.fromOffset(16, 36)
browserList.Size = UDim2.new(1, -32, 1, -88)
browserList.ScrollBarThickness = 4
browserList.ScrollBarImageColor3 = THEME.line
browserList.ScrollingDirection = Enum.ScrollingDirection.Y
browserList.CanvasSize = UDim2.new(0, 0, 0, 0)
browserList.AutomaticCanvasSize = Enum.AutomaticSize.Y
browserList.Parent = browserModal.Body
Kit.round(browserList, 10)
Kit.edge(browserList, THEME.line, 0.2, 0.65)
Kit.padding(browserList, 8, 8, 8, 8)
Kit.vlist(browserList, 4)

local browserButtonsRow, browserButtons = Kit.buttonRow(browserModal.Body, {
    {
        text = "上一级",
        tone = "quiet",
        onClick = function()
            App.browseUp()
        end,
    },
    {
        text = "根目录",
        tone = "quiet",
        onClick = function()
            App.browseRoot()
        end,
    },
    {
        text = "刷新",
        tone = "quiet",
        onClick = function()
            App.refreshBrowser()
        end,
    },
    {
        text = "关闭",
        tone = "ghost",
        onClick = function()
            browserModal:Close()
        end,
    },
}, { order = 0 })
browserButtonsRow.Position = UDim2.new(0, 16, 1, -44)
browserButtonsRow.Size = UDim2.new(1, -32, 0, 32)

local browserDir = ""

function App.setStats(vertices, faces, edges, triangles)
    if UI.statsLabel then
        UI.statsLabel.Text = string.format(
            "顶点 %d · 面 %d · 唯一边 %d · 三角形 %d",
            vertices,
            faces,
            edges,
            triangles
        )
    end
    local values = UI.statValues
    if values then
        values[1].Text = tostring(vertices)
        values[2].Text = tostring(faces)
        values[3].Text = tostring(edges)
        values[4].Text = tostring(triangles)
    end
end
function App.refreshCapabilities()
    if not UI.capabilityLabel then
        return
    end
    local readText = CAPS.readfile and "readfile 可用" or "readfile 缺失（用粘贴模式）"
    local browseText = canBrowseWorkspace and "工作区浏览可用" or "无 listfiles / isfolder"
    local createText = nativePartCreationOk and "Part 创建自检通过" or "Part 创建自检失败"
    UI.capabilityLabel.Text = string.format(
        "执行器：%s\n%s · %s\n%s",
        executorName,
        readText,
        browseText,
        createText
    )
    UI.capabilityLabel.TextColor3 = nativePartCreationOk and THEME.textDim or THEME.err

    if UI.browseButton then
        UI.browseButton:SetDimmed(
            not canBrowseWorkspace,
            "当前执行器没有 listfiles / isfolder，无法浏览目录；请手动输入路径或用粘贴。"
        )
    end
    if UI.readButton then
        UI.readButton:SetDimmed(
            CAPS.readfile == nil,
            "当前执行器没有 readfile，无法按路径读取；请点「粘贴 OBJ」。"
        )
    end
    if UI.autoFindButton then
        UI.autoFindButton:SetDimmed(
            CAPS.listfiles == nil,
            "当前执行器没有 listfiles，无法自动查找；请手动输入路径。"
        )
    end
end

function App.refreshToolStatus()
    if not UI.toolStatusLabel then
        return
    end
    local parts = ReplicatedStorage:FindFirstChild("BuildingParts")
    local plastic = parts and parts:FindFirstChild(CONFIG.ACTUAL_BLOCK_NAME)
    local folder = App.getPlayerBlockFolder()
    local building = App.findTool(CONFIG.ACTUAL_TOOL_BUILD) and "有" or "缺失"
    local scaling = App.findTool(CONFIG.ACTUAL_TOOL_SCALE) and "有" or "缺失"
    local deleting = App.findTool(CONFIG.ACTUAL_TOOL_DELETE) and "有" or "缺失"
    UI.toolStatusLabel.Text = string.format(
        "BuildingTool %s · ScalingTool %s · DeleteTool %s\n塑料块 %s · 积木 ID %s · 建造区 %s",
        building,
        scaling,
        deleting,
        plastic and "存在" or "缺失",
        tostring(App.getPlasticBlockID()),
        folder and "已找到" or "未找到"
    )
    local ready = (building == "有") and (scaling == "有") and plastic and folder
    UI.toolStatusLabel.TextColor3 = ready and THEME.textDim or THEME.warn
end

function App.updateStats()
    if UI.reparseButton then
        UI.reparseButton:SetDimmed(
            State.sourceText == nil,
            "还没有可重新解析的文本；请先读取文件或粘贴 OBJ。"
        )
    end

    local model = State.model
    if not model then
        if UI.sourceLabel then
            UI.sourceLabel.Text = "尚未导入模型"
            UI.sourceLabel.TextColor3 = THEME.textDim
            App.setStats(0, 0, 0, 0)
            UI.warningLabel.Text = "导入后会在这里显示解析警告。"
            UI.warningLabel.TextColor3 = THEME.textDim
            UI.estimateLabel.Text = "预计积木：尚未导入模型"
            UI.estimateLabel.TextColor3 = THEME.textDim
        end
        return
    end

    local name = State.sourceName or "未命名"
    if model.featureInfo then
        name = name .. string.format("（边框模式 ≥ %.0f°）", model.featureInfo.angle)
    end
    if State.needsReparse then
        name = name .. "（设置已更改，待重新解析）"
    end
    UI.sourceLabel.Text = name
    UI.sourceLabel.TextColor3 = THEME.text
    App.setStats(model.vertexCount, model.faceCount, model.edgeCount, model.triangleCount)

    if model.warningCount > 0 then
        local lines = {}
        for index = 1, math.min(2, #model.warnings) do
            lines[#lines + 1] = model.warnings[index]
        end
        if model.warningCount > #lines then
            lines[#lines + 1] = string.format("……共 %d 条警告 / 跳过记录", model.warningCount)
        end
        UI.warningLabel.Text = table.concat(lines, "\n")
        UI.warningLabel.TextColor3 = THEME.warn
    else
        UI.warningLabel.Text = "解析无警告。"
        UI.warningLabel.TextColor3 = THEME.textDim
    end

    if model.featureInfo then
        local featureLine = string.format(
            "边框模式：原 %d 条边 → %d 条特征边（扫描 %d 个三角形，阈值 %.0f°）",
            model.featureInfo.sourceEdgeCount,
            model.featureInfo.edgeCount,
            model.featureInfo.triangleCount,
            model.featureInfo.angle
        )
        if UI.warningLabel.Text == "解析无警告。" then
            UI.warningLabel.Text = featureLine
            UI.warningLabel.TextColor3 = THEME.textDim
        else
            UI.warningLabel.Text = UI.warningLabel.Text .. "\n" .. featureLine
        end
    end

    local maxEdges = math.floor(
        UI.maxEdgeField:Number(1, CONFIG.HARD_MAX_EDGES, CONFIG.DEFAULT_MAX_EDGES, true)
    )
    local autoSimplify = UI.autoSimplifyToggle:Value()
    if model.edgeCount > maxEdges then
        if autoSimplify then
            UI.estimateLabel.Text = string.format(
                "预计积木：≤ %d 根（当前 %d 条边，生成时会自动简化）",
                maxEdges,
                model.edgeCount
            )
            UI.estimateLabel.TextColor3 = THEME.warn
        else
            UI.estimateLabel.Text = string.format(
                "预计积木：%d 条边超过上限 %d；需要提高上限，或打开自动简化",
                model.edgeCount,
                maxEdges
            )
            UI.estimateLabel.TextColor3 = THEME.err
        end
    else
        UI.estimateLabel.Text = string.format(
            "预计积木：%d 根（每条唯一边 = 1 根 Part）",
            model.edgeCount
        )
        UI.estimateLabel.TextColor3 = THEME.textDim
    end

    if model.featureInfo then
        UI.estimateLabel.Text = UI.estimateLabel.Text
            .. string.format("；边框模式：原 %d 条边", model.featureInfo.sourceEdgeCount)
    end

    if State.needsReparse then
        UI.estimateLabel.Text = UI.estimateLabel.Text .. "；设置已更改，需重新解析"
        UI.estimateLabel.TextColor3 = THEME.warn
    end
end

local function resetPreviewCache()
    State.previewRender = nil
    State.previewRenderModel = nil
    State.previewRenderLimit = nil
    State.lastPreviewSimplifyInfo = nil
    if App.clearPreview then
        App.clearPreview(false)
    end
end

local function readWorkspaceFile(path)
    if not CAPS.readfile then
        return nil, "当前执行器没有 readfile"
    end
    local ok, data = pcall(CAPS.readfile, path)
    if not ok then
        return nil, "readfile 失败：" .. tostring(data)
    end
    if type(data) ~= "string" then
        return nil, "readfile 没有返回字符串"
    end
    if #data == 0 then
        return nil, "文件为空"
    end
    if #data > CONFIG.MAX_FILE_BYTES then
        return nil, string.format(
            "文件过大（%.1f MB），上限 %.1f MB",
            #data / 1024 / 1024,
            CONFIG.MAX_FILE_BYTES / 1024 / 1024
        )
    end
    if string.find(data, "\0", 1, true) then
        return nil, "文件含 NUL 字节，可能是 UTF-16 或二进制；请另存为 UTF-8 文本 OBJ"
    end
    return data
end

function App.importFromText(text, name)
    if State.actualBuilding then
        App.status("实际建造中不能重新导入；请先取消实际建造。", "warn")
        return false
    end
    if State.generating then
        App.status("生成中不能重新导入；请先取消生成。", "warn")
        return false
    end
    if State.parsing then
        App.status("已经在解析中。", "warn")
        return false
    end
    if type(text) ~= "string" or text == "" then
        App.status("OBJ 文本为空。", "error")
        return false
    end
    if #text > CONFIG.MAX_FILE_BYTES then
        App.status(string.format(
            "文本过大（%.1f MB），上限 %.1f MB。",
            #text / 1024 / 1024,
            CONFIG.MAX_FILE_BYTES / 1024 / 1024
        ), "error")
        return false
    end

    State.parsing = true
    State.cancelRequested = false
    App.setProgress(0)
    App.status("正在解析 OBJ ...", "info")
    task.wait()

    local triangulateAtStart = UI.triangulateToggle:Value()
    local featureAtStart = UI.borderToggle and UI.borderToggle:Value() or false
    local featureAngleAtStart = UI.borderAngleField
        and UI.borderAngleField:Number(
            CONFIG.MIN_FEATURE_EDGE_ANGLE,
            CONFIG.MAX_FEATURE_EDGE_ANGLE,
            CONFIG.DEFAULT_FEATURE_EDGE_ANGLE
        )
        or CONFIG.DEFAULT_FEATURE_EDGE_ANGLE
    local started = os.clock()
    local ok, model, parseError = pcall(function()
        return Core.parseOBJ(text, {
            triangulate = triangulateAtStart,
            featureEdges = featureAtStart,
            featureAngle = featureAngleAtStart,
            maxVertices = CONFIG.MAX_VERTICES,
            maxFaces = CONFIG.MAX_FACES,
            maxEdges = CONFIG.MAX_PARSED_EDGES,
            maxShellTriangles = CONFIG.MAX_SHELL_TRIANGLES,
            yieldEvery = CONFIG.PARSE_YIELD_LINES,
            yield = function()
                task.wait()
            end,
            onProgress = function(position, total)
                if total > 0 then
                    local alpha = position / total
                    App.setProgress(alpha)
                    App.status(string.format("解析中 ... %d%%", math.floor(alpha * 100)), "info")
                end
            end,
            shouldCancel = function()
                return State.cancelRequested
            end,
        })
    end)
    State.parsing = false

    if not ok then
        App.setProgress(0)
        App.status("解析器内部错误：" .. tostring(model), "error")
        return false
    end
    if not model then
        App.setProgress(0)
        if tostring(parseError) == "已取消" then
            App.status("已取消解析。", "warn")
        else
            App.status("解析失败：" .. tostring(parseError), "error")
        end
        return false
    end

    State.model = model
    State.sourceText = text
    State.sourceName = name or "未命名"
    local featureNow = UI.borderToggle and UI.borderToggle:Value() or false
    local featureAngleNow = UI.borderAngleField
        and UI.borderAngleField:Number(
            CONFIG.MIN_FEATURE_EDGE_ANGLE,
            CONFIG.MAX_FEATURE_EDGE_ANGLE,
            CONFIG.DEFAULT_FEATURE_EDGE_ANGLE
        )
        or CONFIG.DEFAULT_FEATURE_EDGE_ANGLE
    State.needsReparse = (UI.triangulateToggle:Value() ~= triangulateAtStart)
        or (featureNow ~= featureAtStart)
        or (math.abs(featureAngleNow - featureAngleAtStart) > 1e-9)
    State.lastSimplifyInfo = nil
    resetPreviewCache()

    App.updateStats()
    App.setProgress(1)

    local elapsed = os.clock() - started
    local suffix = ""
    if model.warningCount > 0 then
        suffix = string.format("，%d 条警告 / 跳过记录", model.warningCount)
    end
    App.status(string.format(
        "解析完成：%d 顶点 / %d 面 / %d 条唯一边，用时 %.2f 秒%s。",
        model.vertexCount,
        model.faceCount,
        model.edgeCount,
        elapsed,
        suffix
    ), "ok")
    return true
end

function App.importFromPath()
    if isBusy() then
        App.status("当前正在" .. tostring(busyReason()) .. "，请等待或先取消。", "warn")
        return
    end
    local path = cleanPath(UI.pathField:GetText())
    if path == "" then
        App.status("请先填写执行器工作区内的 OBJ 路径。", "error")
        return
    end
    if not CAPS.readfile then
        App.status("当前执行器没有 readfile，无法按路径读取；已打开粘贴框。", "warn")
        App.openPaste()
        return
    end

    UI.pathField:SetText(path)
    App.setProgress(0.05)
    App.status("正在读取：" .. path, "info")
    task.wait()

    local data, readError = readWorkspaceFile(path)
    if not data then
        App.setProgress(0)
        App.status("读取失败：" .. tostring(readError), "error")
        return
    end
    App.importFromText(data, path)
end

function App.reparse()
    if not State.sourceText then
        App.status("没有缓存的 OBJ 文本；请先读取文件或粘贴。", "warn")
        return
    end
    if State.generating or State.parsing then
        App.status("当前正在解析或生成，请稍后。", "warn")
        return
    end
    App.importFromText(State.sourceText, State.sourceName)
end

function App.autoFindObj()
    if isBusy() then
        App.status("当前正在" .. tostring(busyReason()) .. "，请稍后。", "warn")
        return
    end
    if not CAPS.listfiles then
        App.status("当前执行器没有 listfiles，无法自动查找；请手动输入路径或粘贴。", "warn")
        return
    end

    local roots = {
        "", "builds", "Builds", "models", "Models", "saves", "Saves", "obj", "OBJ", "meshes", "Meshes",
    }
    local found = {}
    local seen = {}
    for _, root in ipairs(roots) do
        local rootOk = true
        if root ~= "" and CAPS.isfolder then
            local folderOk, isDirectory = pcall(CAPS.isfolder, root)
            rootOk = folderOk and isDirectory == true
        end
        if rootOk then
            local listOk, entries = pcall(CAPS.listfiles, root)
            if listOk and type(entries) == "table" then
                for _, entry in ipairs(entries) do
                    if type(entry) == "string" then
                        local entryPath = joinPath(root, entry)
                        if string.lower(entryPath):sub(-4) == ".obj" and not seen[entryPath] then
                            seen[entryPath] = true
                            found[#found + 1] = entryPath
                        end
                    end
                end
            end
        end
    end

    table.sort(found)
    print(string.format("[OBJ Wireframe] 自动查找候选：%d 个", #found))
    for index = 1, math.min(10, #found) do
        print("  " .. found[index])
    end

    if #found == 0 then
        App.status(
            "没有在根目录、builds、models、saves 等常见目录找到 .obj；请确认文件在执行器工作区。",
            "error"
        )
        return
    end

    UI.pathField:SetText(found[1])
    if #found == 1 then
        App.status("找到 1 个 .obj：" .. found[1] .. "；请点「读取解析」。", "ok")
        return
    end

    if canBrowseWorkspace then
        browserDir = string.match(found[1], "^(.*)/[^/]*$") or ""
        browserModal:Open()
        App.refreshBrowser()
        App.status(string.format(
            "找到 %d 个 .obj，已填入第一个，同时打开浏览器供选择。",
            #found
        ), "warn")
    else
        App.status(string.format(
            "找到 %d 个 .obj，已填入第一个：%s；请确认路径后点「读取解析」。",
            #found,
            found[1]
        ), "warn")
    end
end

function App.openPaste()
    if isBusy() then
        App.status("当前正在" .. tostring(busyReason()) .. "，请稍后再打开粘贴框。", "warn")
        return
    end
    pasteModal:Open()
    task.defer(function()
        pcall(function()
            pasteBox:CaptureFocus()
        end)
    end)
end

function App.refreshBrowser()
    for _, child in ipairs(browserList:GetChildren()) do
        if child:IsA("TextButton") or child:IsA("TextLabel") then
            child:Destroy()
        end
    end

    local shown = "/" .. ((browserDir == "") and " (工作区根目录)" or (" " .. browserDir))
    browserPathLabel.Text = shown
    browserList.CanvasPosition = Vector2.new(0, 0)

    if not CAPS.listfiles then
        local label = Kit.label(browserList, "当前执行器没有 listfiles，无法浏览。", {
            wrap = true,
            size = 12,
            color = THEME.err,
        })
        label.LayoutOrder = 1
        return
    end

    local ok, entries = pcall(CAPS.listfiles, browserDir)
    if not ok or type(entries) ~= "table" then
        local label = Kit.label(browserList, "listfiles 失败：" .. tostring(entries), {
            wrap = true,
            size = 12,
            color = THEME.err,
        })
        label.LayoutOrder = 1
        return
    end

    local folders = {}
    local files = {}
    local total = 0
    for _, entry in ipairs(entries) do
        if type(entry) == "string" and entry ~= "" and entry ~= "." and entry ~= ".." then
            total = total + 1
            if total <= 1500 then
                local entryPath = joinPath(browserDir, entry)
                local isDirectory = false
                if CAPS.isfolder then
                    local folderOk, folderResult = pcall(CAPS.isfolder, entryPath)
                    isDirectory = (folderOk and folderResult == true)
                end
                local name = entryNameOf(entryPath)
                if isDirectory then
                    folders[#folders + 1] = { path = entryPath, name = name }
                elseif string.lower(entryPath):sub(-4) == ".obj" then
                    files[#files + 1] = { path = entryPath, name = name }
                end
            end
        end
    end

    table.sort(folders, function(a, b)
        return string.lower(a.name) < string.lower(b.name)
    end)
    table.sort(files, function(a, b)
        return string.lower(a.name) < string.lower(b.name)
    end)

    local order = 0
    local function addEntry(entry, isDirectory)
        order = order + 1
        local button = Kit.button(
            browserList,
            (isDirectory and "[目录] " or "[OBJ] ") .. entry.name,
            { tone = isDirectory and "quiet" or "default", height = 26 }
        )
        button.Instance.LayoutOrder = order
        button.Instance.TextXAlignment = Enum.TextXAlignment.Left
        button:OnClick(function()
            if isDirectory then
                browserDir = entry.path
                App.refreshBrowser()
            else
                UI.pathField:SetText(entry.path)
                browserModal:Close()
                App.status("已选择：" .. entry.path, "ok")
            end
        end)
    end

    for _, folder in ipairs(folders) do
        addEntry(folder, true)
    end
    for _, file in ipairs(files) do
        addEntry(file, false)
    end

    if #folders == 0 and #files == 0 then
        local label = Kit.label(browserList, "当前目录没有 .obj 文件或子目录。", {
            wrap = true,
            size = 12,
            color = THEME.textDim,
        })
        label.LayoutOrder = 1
    end
end

function App.browseUp()
    local normalized = normalizeSlashes(browserDir)
    browserDir = string.match(normalized, "^(.*)/[^/]*$") or ""
    App.refreshBrowser()
end

function App.browseRoot()
    browserDir = ""
    App.refreshBrowser()
end

function App.openBrowser()
    if not canBrowseWorkspace then
        App.status("当前执行器没有 listfiles / isfolder，无法浏览；请手动输入路径。", "warn")
        return
    end
    if isBusy() then
        App.status("当前正在" .. tostring(busyReason()) .. "，请稍后再浏览。", "warn")
        return
    end

    local current = normalizeSlashes(cleanPath(UI.pathField:GetText()))
    local directory = string.match(current, "^(.*)/[^/]*$")
    if not directory and current ~= "" and CAPS.isfolder then
        local ok, isDirectory = pcall(CAPS.isfolder, current)
        if ok and isDirectory == true then
            directory = current
        end
    end
    browserDir = directory or ""
    browserModal:Open()
    App.refreshBrowser()
end

function App.getPivot()
    if State.pivotMode == "origin" then
        return 0, 0, 0
    end
    if State.pivotMode == "custom" then
        return UI.customPivotTriple:Numbers(-1000000000, 1000000000, 0)
    end
    local model = State.model
    if model then
        return model.center[1], model.center[2], model.center[3]
    end
    return 0, 0, 0
end

function App.readTransformParams()
    local model = State.model
    if not model then
        return nil, "请先导入 OBJ。"
    end

    local scale = UI.scaleField:Number(0.000001, 100000, 1)
    local rotationX, rotationY, rotationZ = UI.rotationTriple:Numbers(-360000, 360000, 0)
    local positionX, positionY, positionZ = UI.positionTriple:Numbers(-1e9, 1e9, 0)
    local thickness = UI.thicknessField:Number(CONFIG.MIN_PART_SIZE, 5, CONFIG.DEFAULT_THICKNESS)
    local maxEdges = math.floor(
        UI.maxEdgeField:Number(1, CONFIG.HARD_MAX_EDGES, CONFIG.DEFAULT_MAX_EDGES, true)
    )
    local pivotX, pivotY, pivotZ = App.getPivot()

    local scaledMax = math.max(model.size[1], model.size[2], model.size[3]) * scale
    if scaledMax > CONFIG.MAX_PART_LENGTH then
        return nil, string.format(
            "缩放后包围盒 %.1f studs 超过单根 Part 上限 %d；请降低缩放。",
            scaledMax,
            CONFIG.MAX_PART_LENGTH
        )
    end

    local rotation = CFrame.fromEulerAnglesXYZ(
        math.rad(rotationX),
        math.rad(rotationY),
        math.rad(rotationZ)
    )
    local worldPosition = Vector3.new(positionX, positionY, positionZ)

    local function transformPoint(x, y, z)
        local localPoint = Vector3.new(
            (x - pivotX) * scale,
            (y - pivotY) * scale,
            (z - pivotZ) * scale
        )
        return worldPosition + rotation:VectorToWorldSpace(localPoint)
    end

    return {
        model = model,
        scale = scale,
        rotation = rotation,
        worldPosition = worldPosition,
        thickness = thickness,
        maxEdges = maxEdges,
        scaledMax = scaledMax,
        pivotX = pivotX,
        pivotY = pivotY,
        pivotZ = pivotZ,
        transformPoint = transformPoint,
    }
end

function App.refreshPivotUI()
    for mode, button in pairs(UI.pivotButtons or {}) do
        button:SetTone((State.pivotMode == mode) and "accent" or "default")
    end
    if UI.customPivotRow then
        UI.customPivotRow.Visible = (State.pivotMode == "custom")
    end
end

function App.applyFit()
    local model = State.model
    if not model then
        App.status("请先导入模型。", "error")
        return
    end
    local target = UI.targetSizeField:Number(1, CONFIG.MAX_PART_LENGTH, CONFIG.DEFAULT_TARGET_SIZE)
    local largest = math.max(model.size[1], model.size[2], model.size[3])
    if largest <= 1e-9 then
        App.status("模型包围盒尺寸为 0，无法计算适配缩放。", "error")
        return
    end
    local requested = target / largest
    local applied = clamp(requested, 0.000001, 100000)
    UI.scaleField:SetText(formatNumber(applied))
    if math.abs(applied - requested) > 1e-9 then
        App.status(string.format(
            "目标需要缩放 %.3g，但允许范围是 1e-6 到 1e5；已用 %s，实际尺寸会偏离目标。",
            requested,
            formatNumber(applied)
        ), "warn")
    else
        App.status(string.format(
            "已设置缩放 %s；缩放后最大包围盒约 %.1f studs。",
            formatNumber(applied),
            largest * applied
        ), "ok")
    end
    App.onTransformChanged()
end

function App.applyPlaceInFront()
    local camera = Workspace.CurrentCamera
    if not camera then
        App.status("当前没有 Workspace.CurrentCamera。", "error")
        return
    end

    local scale = UI.scaleField:Number(0.000001, 100000, 1)
    local model = State.model
    local modelSize = 10
    if model then
        modelSize = math.max(model.size[1], model.size[2], model.size[3]) * scale
    end
    local distance = math.max(12, modelSize * 1.35)
    local origin = camera.CFrame.Position
    local target = origin + camera.CFrame.LookVector * distance

    if not isFinite(target.X) or not isFinite(target.Y) or not isFinite(target.Z)
        or not isFinite(origin.X) or not isFinite(origin.Y) or not isFinite(origin.Z)
    then
        App.status("相机位置或缩放数值无效，无法计算前方位置。", "error")
        return
    end

    UI.positionTriple:SetTexts(formatNumber(target.X), formatNumber(target.Y), formatNumber(target.Z))
    App.status(string.format(
        "锚点已放到相机前方约 %.1f studs：%s, %s, %s。",
        distance,
        formatNumber(target.X),
        formatNumber(target.Y),
        formatNumber(target.Z)
    ), "ok")
    App.onTransformChanged()
end

function App.onTransformChanged()
    if State.previewVisible and App.schedulePreviewRefresh then
        App.schedulePreviewRefresh()
    end
end

function App.clearGenerated(showStatus)
    if State.folder then
        pcall(function()
            State.folder:Destroy()
        end)
    end
    State.folder = nil
    State.generatedCount = 0
    if showStatus then
        App.setProgress(0)
        App.status("已清除本脚本生成的线框；其他脚本或玩家创建的东西不受影响。", "ok")
    end
end

function App.cancelAll()
    if State.actualBuilding or State.previewBuilding or State.generating or State.parsing then
        State.cancelRequested = true
        App.status("正在取消 ...", "warn")
    else
        App.status("当前没有正在进行的解析、生成、预览或建造。", "info")
    end
end

function App.clearWireframe()
    if State.actualBuilding then
        State.cancelRequested = true
        App.status("正在取消实际建造并清理本次结果 ...", "warn")
        return
    end
    if State.generating then
        State.cancelRequested = true
        State.clearOnCancel = true
        App.status("正在取消生成并清理本次部分结果 ...", "warn")
        return
    end
    if State.parsing then
        State.cancelRequested = true
    end
    App.clearGenerated(true)
end

function App.prepareRender(maxEdges, onProgress)
    local model = State.model
    if not model then
        return nil, "请先导入 OBJ。"
    end

    if model.edgeCount <= maxEdges then
        local render, renderError = Core.buildRenderEdges(model, nil, false)
        if render and onProgress then
            onProgress(1)
        end
        return render, renderError, nil
    end

    local render, renderError = Core.simplifyModel(model, maxEdges, {
        iterations = 14,
        yield = function()
            task.wait()
        end,
        onProgress = function(iteration, total)
            if onProgress and total > 0 then
                onProgress(iteration / total)
            end
        end,
        shouldCancel = function()
            return State.cancelRequested
        end,
    })

    local simplifyInfo
    if render then
        simplifyInfo = {
            sourceEdgeCount = model.edgeCount,
            count = render.count,
            gridSize = render.gridSize,
            sampled = render.sampled == true,
        }
    end
    return render, renderError, simplifyInfo
end

function App.startGeneration()
    if State.actualBuilding then
        App.status("实际建造进行中，不能同时生成本地线框。", "warn")
        return
    end
    if State.generating or State.parsing then
        App.status("当前正在解析或生成，请等待或先取消。", "warn")
        return
    end
    if not nativePartCreationOk then
        App.status("原生 Part 创建自检失败，当前环境无法生成积木。", "error")
        return
    end
    if State.needsReparse and State.sourceText then
        local ok = App.importFromText(State.sourceText, State.sourceName)
        if not ok then
            return
        end
    end

    local model = State.model
    if not model then
        App.status("请先导入 OBJ。", "error")
        return
    end

    local params, paramsError = App.readTransformParams()
    if not params then
        App.status(paramsError, "error")
        return
    end
    if model.edgeCount > params.maxEdges and not UI.autoSimplifyToggle:Value() then
        App.status(string.format(
            "模型有 %d 条边，超过上限 %d；请提高上限，或打开自动简化。",
            model.edgeCount,
            params.maxEdges
        ), "error")
        return
    end

    State.cancelRequested = false
    State.clearOnCancel = false
    State.generating = true
    State.lastSimplifyInfo = nil
    App.setProgress(0)
    App.status("准备边数据 ...", "info")
    task.wait()

    local function stop(message, kind)
        State.generating = false
        App.setProgress(0)
        if State.clearOnCancel and State.cancelRequested then
            App.clearGenerated(false)
            State.clearOnCancel = false
            App.status("已取消并清理本次部分结果。", "warn")
        else
            State.clearOnCancel = false
            App.status(message, kind)
        end
    end

    local render, renderError, simplifyInfo = App.prepareRender(params.maxEdges, function(alpha)
        App.setProgress(alpha * 0.35)
        App.status(string.format("准备网格 ... %d%%", math.floor(alpha * 100)), "info")
    end)
    State.lastSimplifyInfo = simplifyInfo

    if not render then
        if tostring(renderError) == "已取消" then
            stop("已取消生成。", "warn")
        else
            stop("准备网格失败：" .. tostring(renderError), "error")
        end
        return
    end
    if render.count > CONFIG.HARD_MAX_EDGES then
        stop(string.format("最终 %d 条边超过硬上限 %d。", render.count, CONFIG.HARD_MAX_EDGES), "error")
        return
    end
    if render.count == 0 then
        stop("没有可生成的边。", "error")
        return
    end
    if State.cancelRequested then
        stop("已取消生成。", "warn")
        return
    end

    local folderCreateOk, folderOrError = pcall(function()
        local newFolder = Instance.new("Folder")
        newFolder.Name = CONFIG.FOLDER_PREFIX .. tostring(os.time())
        newFolder.Parent = Workspace
        return newFolder
    end)
    if not folderCreateOk then
        stop("创建线框文件夹失败：" .. tostring(folderOrError), "error")
        return
    end

    App.clearGenerated(false)
    State.folder = folderOrError
    State.generatedCount = 0

    local template = Instance.new("Part")
    template.Name = "OBJEdgeTemplate"
    template.Anchored = true
    template.CanCollide = false
    template.CanTouch = false
    template.CanQuery = false
    template.CastShadow = false
    template.Massless = true
    template.Locked = true
    template.TopSurface = Enum.SurfaceType.Smooth
    template.BottomSurface = Enum.SurfaceType.Smooth
    template.Material = CONFIG.MATERIAL
    template.Color = CONFIG.DEFAULT_COLOR
    template.Transparency = 0
    template.Size = Vector3.new(1, params.thickness, params.thickness)

    local created = 0
    local skipped = 0
    local failed = 0
    local tooLong = 0
    local total = render.count
    local baseProgress = simplifyInfo and 0.35 or 0
    local lastProgress = baseProgress
    local index = 1

    while index <= total do
        if State.cancelRequested then
            break
        end

        local last = math.min(index + CONFIG.BATCH_SIZE - 1, total)
        for edgeIndex = index, last do
            local pointA = params.transformPoint(
                render.ax[edgeIndex],
                render.ay[edgeIndex],
                render.az[edgeIndex]
            )
            local pointB = params.transformPoint(
                render.bx[edgeIndex],
                render.by[edgeIndex],
                render.bz[edgeIndex]
            )
            local basis = Core.computeEdgeBasis(
                pointA.X, pointA.Y, pointA.Z,
                pointB.X, pointB.Y, pointB.Z
            )
            if not basis then
                skipped = skipped + 1
            elseif basis.length > CONFIG.MAX_PART_LENGTH then
                tooLong = tooLong + 1
            else
                local ok = pcall(function()
                    local part = template:Clone()
                    part.Name = string.format("Edge_%06d", edgeIndex)
                    part.Size = Vector3.new(
                        math.max(basis.length, CONFIG.MIN_PART_SIZE),
                        params.thickness,
                        params.thickness
                    )
                    part.CFrame = CFrame.fromMatrix(
                        Vector3.new(basis.mx, basis.my, basis.mz),
                        Vector3.new(basis.xx, basis.xy, basis.xz),
                        Vector3.new(basis.yx, basis.yy, basis.yz),
                        Vector3.new(basis.zx, basis.zy, basis.zz)
                    )
                    part.Parent = State.folder
                end)
                if ok then
                    created = created + 1
                else
                    failed = failed + 1
                end
            end
        end

        State.generatedCount = created
        lastProgress = baseProgress + (1 - baseProgress) * (last / total)
        App.setProgress(lastProgress)
        App.status(string.format("生成中 ... %d / %d 根", last, total), "info")

        if State.folder == nil or State.folder.Parent == nil then
            break
        end

        index = last + 1
        task.wait()
    end

    template:Destroy()
    State.generating = false
    State.generatedCount = created

    if State.clearOnCancel and State.cancelRequested then
        App.clearGenerated(false)
        State.clearOnCancel = false
        App.setProgress(0)
        App.status("生成已取消，已清理本次生成的部分线框。", "warn")
        return
    end

    if State.cancelRequested then
        App.setProgress(lastProgress)
        App.status(string.format("已取消：保留已生成的 %d 根线框，可点「清除线框」。", created), "warn")
        return
    end

    if not State.folder then
        App.setProgress(0)
        App.status("线框文件夹已被外部删除，生成结果不再可见。", "error")
        return
    end

    if created == 0 then
        App.clearGenerated(false)
        App.setProgress(0)
        App.status("没有成功生成任何积木；请检查缩放、位置与 Part 创建权限。", "error")
        return
    end

    App.setProgress(1)
    local details = {}
    if simplifyInfo then
        if simplifyInfo.sampled then
            details[#details + 1] = string.format(
                "聚类不可用，改为均匀采样 %d → %d 边",
                simplifyInfo.sourceEdgeCount,
                simplifyInfo.count
            )
        else
            details[#details + 1] = string.format(
                "简化 %d → %d 边（格距 %.3g）",
                simplifyInfo.sourceEdgeCount,
                simplifyInfo.count,
                simplifyInfo.gridSize or 0
            )
        end
    end
    if skipped > 0 then
        details[#details + 1] = string.format("跳过退化边 %d", skipped)
    end
    if tooLong > 0 then
        details[#details + 1] = string.format("跳过超长边 %d", tooLong)
    end
    if failed > 0 then
        details[#details + 1] = string.format("创建失败 %d", failed)
    end

    local message = string.format("完成：生成 %d 根线框积木。", created)
    if #details > 0 then
        message = message .. " " .. table.concat(details, "；") .. "。"
    end
    App.status(message, "ok")
end

local buildPage = newPage(4, "Build")

local previewCard = Kit.card(buildPage, "预览 · 仅本机可见", 1, { index = 1 })

local previewRow, previewButtons = Kit.buttonRow(previewCard, {
    {
        text = "显示预览（实际外观）",
        accent = true,
        onClick = function()
            App.togglePreview()
        end,
    },
}, { order = 1 })
UI.previewButton = previewButtons[1]

Kit.hint(
    previewCard,
    "预览只在你自己的客户端创建 Part：按 PlasticBlock 的真实颜色 / 材质 / 透明度显示，"
        .. "并在锚点画出世界 XYZ 三色轴（X 红 / Y 绿 / Z 蓝）。"
        .. "打开后修改缩放、旋转、位置、粗细、边数会自动防抖刷新。",
    2
)

local actualCard = Kit.card(buildPage, "实际建造 · 消耗服务器库存", 2, { index = 2 })

local actualRow, actualButtons = Kit.buttonRow(actualCard, {
    {
        text = "实际建造（塑料）",
        accent = true,
        onClick = function()
            App.startActualBuild(false)
        end,
    },
    {
        text = "清除实际建造",
        tone = "danger",
        onClick = function()
            App.clearActualBuild()
        end,
    },
}, { order = 1 })
UI.actualBuildButton = actualButtons[1]
UI.clearActualButton = actualButtons[2]

local areaRow, areaButtons = Kit.buttonRow(actualCard, {
    {
        text = "清空建造区（连点两次确认）",
        tone = "quiet",
        onClick = function()
            App.clearBuildArea()
        end,
    },
}, { order = 2, height = 30 })
UI.clearAreaButton = areaButtons[1]

Kit.hint(
    actualCard,
    "流程：高空暂存 → 等服务器真的生成 → 按 Y 坐标对上槽位 → 用 ScalingTool 缩放旋转到目标位置。"
        .. "收不到块通常是库存、积木上限或限流；反复失败留下的残块会一直占额度，"
        .. "所以先「清空建造区」再重试，比反复硬建有效。",
    3
)

local toolCard = Kit.card(buildPage, "环境检测", 3, { index = 3 })

local toolStatusLabel = Kit.label(toolCard, "工具检测中 ...", {
    wrap = true,
    size = 11,
    color = THEME.textDim,
    valign = Enum.TextYAlignment.Top,
    order = 1,
})
UI.toolStatusLabel = toolStatusLabel

local toolRow, toolButtons = Kit.buttonRow(toolCard, {
    {
        text = "重新检测工具",
        tone = "quiet",
        onClick = function()
            App.refreshToolStatus()
            App.status("已重新检测建造工具与建造区。", "ok")
        end,
    },
}, { order = 2, height = 30 })
UI.refreshToolButton = toolButtons[1]

local shellPage = newPage(5, "Shell")

local shellParamCard = Kit.card(shellPage, "A 方案参数", 1, { index = 1 })

UI.shellThicknessField = Kit.field(
    shellParamCard,
    "外壳板厚",
    tostring(CONFIG.DEFAULT_SHELL_THICKNESS),
    {
        order = 1,
        labelWidth = 118,
        step = 0.01,
        min = CONFIG.MIN_PART_SIZE,
        max = 5,
        fallback = CONFIG.DEFAULT_SHELL_THICKNESS,
    }
)

UI.shellPlateField = Kit.field(
    shellParamCard,
    "体素尺寸",
    tostring(CONFIG.DEFAULT_SHELL_PLATE_SIZE),
    {
        order = 2,
        labelWidth = 118,
        step = 0.1,
        min = CONFIG.MIN_SHELL_PLATE_SIZE,
        max = CONFIG.MAX_SHELL_PLATE_SIZE,
        fallback = CONFIG.DEFAULT_SHELL_PLATE_SIZE,
    }
)

UI.shellBudgetField = Kit.field(
    shellParamCard,
    "最大积木数",
    tostring(CONFIG.DEFAULT_SHELL_BUDGET),
    {
        order = 3,
        labelWidth = 118,
        step = 1000,
        min = 100,
        max = CONFIG.MAX_SHELL_BUDGET,
        fallback = CONFIG.DEFAULT_SHELL_BUDGET,
    }
)

Kit.hint(
    shellParamCard,
    string.format(
        "体素越小越平滑，块数越多（%.1f - %d studs）。超预算会自动加粗重试，"
            .. "加到 %d studs 仍超限才报错。",
        CONFIG.MIN_SHELL_PLATE_SIZE,
        CONFIG.MAX_SHELL_PLATE_SIZE,
        CONFIG.MAX_SHELL_PLATE_SIZE
    ),
    4
)

local shellRunCard = Kit.card(shellPage, "执行", 2, { index = 2 })

local shellRow, shellButtons = Kit.buttonRow(shellRunCard, {
    {
        text = "实际建造完整模型（体素 + 倒角）",
        accent = true,
        onClick = function()
            App.startActualBuild(true)
        end,
    },
}, { order = 1 })
UI.shellBuildButton = shellButtons[1]

Kit.hint(
    shellRunCard,
    "全模型共用一套世界体素格：三角形只标记表面经过的格子，同一格只出一块，法线取平均，"
        .. "所以相邻面天然对齐，不会在交界处各切各的网格。相邻面夹角超过 "
        .. string.format("%d°", CONFIG.SHELL_BEVEL_ANGLE)
        .. " 的硬边会额外铺倒角条压住轮廓。"
        .. "方块不能裁成斜面，表面仍是半格到一格的台阶近似，不是精确三角面。",
    2
)
function App.clearPreview(showStatus)
    State.previewToken = State.previewToken + 1
    State.previewBuilding = false
    State.previewVisible = false
    State.previewPending = false
    if State.previewFolder then
        pcall(function()
            State.previewFolder:Destroy()
        end)
    end
    State.previewFolder = nil
    if UI.previewButton then
        UI.previewButton:SetLabel("显示预览（实际外观）")
        UI.previewButton:SetTone("accent")
    end
    if showStatus then
        App.status("已关闭预览。", "info")
    end
end

local function getPreviewStyle()
    local buildingParts = ReplicatedStorage:FindFirstChild("BuildingParts")
    local plastic = buildingParts and buildingParts:FindFirstChild(CONFIG.ACTUAL_BLOCK_NAME)
    local primary
    if plastic then
        if plastic:IsA("BasePart") then
            primary = plastic
        elseif plastic:IsA("Model") then
            primary = plastic.PrimaryPart or plastic:FindFirstChildWhichIsA("BasePart", true)
        end
    end
    if primary and primary:IsA("BasePart") then
        return primary.Color, primary.Material, primary.Transparency, primary.Reflectance
    end
    return CONFIG.PREVIEW_COLOR, Enum.Material.Neon, CONFIG.PREVIEW_TRANSPARENCY, 0
end

local function addAxisGizmo(folder, params)
    local axisLength = CONFIG.PREVIEW_AXIS_LENGTH
    local axisThickness = 0.22

    local function axisPart(name, size, offset, color, label)
        local part = Instance.new("Part")
        part.Name = name
        part.Anchored = true
        part.CanCollide = false
        part.CanTouch = false
        part.CanQuery = false
        part.CastShadow = false
        part.Material = Enum.Material.Neon
        part.Color = color
        part.Transparency = 0.18
        part.Size = size
        part.CFrame = CFrame.new(params.worldPosition + offset)
        part.Parent = folder

        local billboard = Instance.new("BillboardGui")
        billboard.Size = UDim2.fromOffset(28, 20)
        billboard.AlwaysOnTop = true
        billboard.MaxDistance = 160
        billboard.Adornee = part
        billboard.Parent = part

        local text = Instance.new("TextLabel")
        text.BackgroundTransparency = 1
        text.Size = UDim2.fromScale(1, 1)
        text.Text = label
        text.TextColor3 = color
        text.TextScaled = true
        text.Font = Enum.Font.GothamBold
        text.TextStrokeTransparency = 0.35
        text.Parent = billboard
    end

    axisPart(
        "Axis_X",
        Vector3.new(axisLength, axisThickness, axisThickness),
        Vector3.new(axisLength * 0.5, 0, 0),
        Color3.fromRGB(255, 82, 82),
        "X"
    )
    axisPart(
        "Axis_Y",
        Vector3.new(axisThickness, axisLength, axisThickness),
        Vector3.new(0, axisLength * 0.5, 0),
        Color3.fromRGB(80, 235, 120),
        "Y"
    )
    axisPart(
        "Axis_Z",
        Vector3.new(axisThickness, axisThickness, axisLength),
        Vector3.new(0, 0, axisLength * 0.5),
        Color3.fromRGB(80, 150, 255),
        "Z"
    )

    local origin = Instance.new("Part")
    origin.Name = "Axis_Origin"
    origin.Shape = Enum.PartType.Ball
    origin.Anchored = true
    origin.CanCollide = false
    origin.CanTouch = false
    origin.CanQuery = false
    origin.CastShadow = false
    origin.Material = Enum.Material.Neon
    origin.Color = Color3.fromRGB(255, 255, 255)
    origin.Size = Vector3.new(0.45, 0.45, 0.45)
    origin.CFrame = CFrame.new(params.worldPosition)
    origin.Parent = folder
end

local function getPreviewRender(params)
    local limit = math.min(CONFIG.PREVIEW_MAX_EDGES, params.maxEdges)
    if State.previewRender
        and State.previewRenderModel == State.model
        and State.previewRenderLimit == limit
    then
        return State.previewRender, nil, State.lastPreviewSimplifyInfo
    end

    local render, renderError, simplifyInfo = App.prepareRender(limit, function(alpha)
        App.setProgress(alpha * 0.62)
        App.status(string.format("准备预览网格 ... %d%%", math.floor(alpha * 100)), "info")
    end)

    if render then
        State.previewRender = render
        State.previewRenderModel = State.model
        State.previewRenderLimit = limit
        State.lastPreviewSimplifyInfo = simplifyInfo
    end
    return render, renderError, simplifyInfo
end

function App.buildPreview(showStatus)
    if State.parsing or State.generating or State.actualBuilding then
        App.status("正在" .. tostring(busyReason()) .. "，请稍后再预览。", "warn")
        return
    end
    if not State.model then
        App.status("请先导入 OBJ。", "error")
        return
    end
    if State.previewBuilding then
        State.previewPending = true
        return
    end
    if State.needsReparse and State.sourceText then
        if not App.importFromText(State.sourceText, State.sourceName) then
            return
        end
    end

    local params, paramsError = App.readTransformParams()
    if not params then
        App.status(paramsError, "error")
        return
    end

    App.clearPreview(false)
    local token = State.previewToken
    State.previewBuilding = true
    State.previewVisible = true
    State.cancelRequested = false
    if UI.previewButton then
        UI.previewButton:SetLabel("刷新预览中 ...")
    end
    App.setProgress(0)
    App.status("准备预览 ...", "info")
    task.wait()

    local render, renderError, simplifyInfo = getPreviewRender(params)
    if token ~= State.previewToken then
        return
    end
    if not render then
        App.clearPreview(false)
        if tostring(renderError) == "已取消" then
            App.status("已取消预览。", "warn")
        else
            App.status("预览准备失败：" .. tostring(renderError), "error")
        end
        return
    end
    if render.count == 0 then
        App.clearPreview(false)
        App.status("没有可预览的边。", "error")
        return
    end
    if State.cancelRequested then
        App.clearPreview(false)
        App.status("已取消预览。", "warn")
        return
    end

    local folder = Instance.new("Folder")
    folder.Name = "OBJ_Wireframe_Preview"
    folder.Parent = Workspace
    State.previewFolder = folder
    addAxisGizmo(folder, params)

    local previewColor, previewMaterial, previewTransparency, previewReflectance = getPreviewStyle()
    local template = Instance.new("Part")
    template.Name = "PreviewEdgeTemplate"
    template.Anchored = true
    template.CanCollide = false
    template.CanTouch = false
    template.CanQuery = false
    template.CastShadow = false
    template.Material = previewMaterial
    template.Color = previewColor
    template.Transparency = previewTransparency
    template.Reflectance = previewReflectance
    template.Size = Vector3.new(params.thickness, params.thickness, 1)

    local total = render.count
    local created = 0
    local skipped = 0
    local index = 1

    while index <= total do
        if token ~= State.previewToken or State.cancelRequested then
            break
        end

        local last = math.min(index + CONFIG.PREVIEW_BATCH - 1, total)
        for edgeIndex = index, last do
            local pointA = params.transformPoint(
                render.ax[edgeIndex],
                render.ay[edgeIndex],
                render.az[edgeIndex]
            )
            local pointB = params.transformPoint(
                render.bx[edgeIndex],
                render.by[edgeIndex],
                render.bz[edgeIndex]
            )
            local dx = pointB.X - pointA.X
            local dy = pointB.Y - pointA.Y
            local dz = pointB.Z - pointA.Z
            local length = math.sqrt(dx * dx + dy * dy + dz * dz)
            if length > 1e-6 and length <= CONFIG.MAX_PART_LENGTH then
                local middle = Vector3.new(
                    (pointA.X + pointB.X) * 0.5,
                    (pointA.Y + pointB.Y) * 0.5,
                    (pointA.Z + pointB.Z) * 0.5
                )
                local direction = Vector3.new(dx / length, dy / length, dz / length)
                local ok = pcall(function()
                    local part = template:Clone()
                    part.Name = string.format("PreviewEdge_%06d", edgeIndex)
                    part.Size = Vector3.new(
                        params.thickness,
                        params.thickness,
                        math.max(
                            math.min(length + params.thickness, CONFIG.MAX_PART_LENGTH),
                            params.thickness
                        )
                    )
                    part.CFrame = CFrame.lookAt(middle, middle + direction)
                    part.Parent = folder
                end)
                if ok then
                    created = created + 1
                else
                    skipped = skipped + 1
                end
            else
                skipped = skipped + 1
            end
        end

        App.setProgress(0.62 + 0.38 * (last / total))
        App.status(string.format("预览中 ... %d / %d 根", last, total), "info")
        if token ~= State.previewToken or State.previewFolder ~= folder or folder.Parent == nil then
            break
        end
        index = last + 1
        task.wait()
    end

    template:Destroy()
    if token ~= State.previewToken then
        return
    end

    State.previewBuilding = false
    if State.cancelRequested then
        App.clearPreview(false)
        App.status("已取消预览。", "warn")
    elseif created == 0 then
        App.clearPreview(false)
        App.status("预览没有成功创建任何 Part。", "error")
    else
        State.previewVisible = true
        if UI.previewButton then
            UI.previewButton:SetLabel("关闭预览")
            UI.previewButton:SetTone("default")
        end
        App.setProgress(1)
        local details = ""
        if simplifyInfo then
            details = string.format(
                "（预览简化 %d → %d 边）",
                simplifyInfo.sourceEdgeCount,
                simplifyInfo.count
            )
        end
        if skipped > 0 then
            details = details .. string.format("，跳过 %d 条退化 / 超长边", skipped)
        end
        if showStatus then
            App.status(string.format(
                "预览完成：%d 根（按实际 PlasticBlock 外观）%s。X 红 / Y 绿 / Z 蓝 为世界轴。",
                created,
                details
            ), "ok")
        end
    end

    if State.previewPending and State.previewVisible then
        State.previewPending = false
        App.schedulePreviewRefresh()
    end
end

function App.schedulePreviewRefresh()
    if not State.previewVisible then
        return
    end
    if State.previewBuilding then
        State.previewPending = true
        return
    end
    if State.parsing or State.generating or State.actualBuilding then
        return
    end

    State.previewToken = State.previewToken + 1
    local token = State.previewToken
    task.delay(CONFIG.PREVIEW_DEBOUNCE, function()
        if token == State.previewToken and State.previewVisible then
            pcall(App.buildPreview, false)
        end
    end)
end

function App.togglePreview()
    if State.previewVisible then
        App.clearPreview(true)
    else
        App.buildPreview(true)
    end
end

function App.findTool(toolName)
    local character = LocalPlayer.Character
    local characterTool = character and character:FindFirstChild(toolName)
    if characterTool and characterTool:IsA("Tool") then
        return characterTool
    end
    local backpack = LocalPlayer:FindFirstChild("Backpack")
    local backpackTool = backpack and backpack:FindFirstChild(toolName)
    if backpackTool and backpackTool:IsA("Tool") then
        return backpackTool
    end
    return nil
end

function App.equipTool(toolName)
    local tool = App.findTool(toolName)
    if not tool then
        return nil
    end
    local character = LocalPlayer.Character
    if not character then
        return nil
    end
    if tool.Parent == character then
        return tool
    end

    local humanoid = character:FindFirstChildOfClass("Humanoid")
    if not humanoid then
        return nil
    end

    local equipped = character:FindFirstChildOfClass("Tool")
    if equipped and equipped ~= tool then
        pcall(function()
            humanoid:UnequipTools()
        end)
        task.wait(0.15)
    end

    local ok = pcall(function()
        humanoid:EquipTool(tool)
    end)
    if not ok then
        return nil
    end
    task.wait(0.25)
    local equippedTool = character:FindFirstChild(toolName)
    if equippedTool and equippedTool:IsA("Tool") then
        return equippedTool
    end
    return nil
end

function App.getPlasticBlockID()
    local data = LocalPlayer:FindFirstChild("Data")
    local value = data and data:FindFirstChild("PlasticBlock")
    if value and value:IsA("ValueBase") then
        return tonumber(value.Value) or 9
    end
    return 9
end

function App.getPlayerBlockFolder()
    local blocks = Workspace:FindFirstChild("Blocks")
    return blocks and blocks:FindFirstChild(LocalPlayer.Name) or nil
end

function App.applyScale(scaleInvoke, block, frame)
    local ok, returnedSize, returnedCFrame = pcall(function()
        return scaleInvoke:InvokeServer(block, frame.size, frame.cframe)
    end)
    if not ok or not block.Parent or not block.PrimaryPart then
        return false
    end
    if typeof(returnedSize) == "Vector3" then
        block.PrimaryPart.Size = returnedSize
    else
        block.PrimaryPart.Size = frame.size
    end
    if typeof(returnedCFrame) == "CFrame" then
        block.PrimaryPart.CFrame = returnedCFrame
    else
        block.PrimaryPart.CFrame = frame.cframe
    end
    return true
end

function App.deleteModelsWithTool(models)
    local serverDeleted = 0
    local localOnly = 0
    local total = #models
    if total == 0 then
        return serverDeleted, localOnly
    end

    local tool = App.equipTool(CONFIG.ACTUAL_TOOL_DELETE)
    local invoke = tool and tool:FindFirstChild("RF")
    if invoke and not invoke:IsA("RemoteFunction") then
        invoke = nil
    end

    local pending = 0
    local maxInFlight = CONFIG.ACTUAL_DELETE_MAX_IN_FLIGHT
    local index = 1
    local nextStatus = 0
    while index <= total do
        while index <= total and pending < maxInFlight do
            local model = models[index]
            index = index + 1
            if model and model.Parent then
                pending = pending + 1
                task.spawn(function()
                    local deletedByServer = false
                    if invoke then
                        local ok = pcall(function()
                            invoke:InvokeServer(model)
                        end)
                        deletedByServer = ok
                    end
                    pcall(function()
                        model:Destroy()
                    end)
                    if deletedByServer then
                        serverDeleted = serverDeleted + 1
                    else
                        localOnly = localOnly + 1
                    end
                    pending = pending - 1
                end)
            end
        end
        local now = os.clock()
        if now >= nextStatus then
            nextStatus = now + 0.25
            App.status(string.format(
                "删除积木 ... %d / %d",
                math.min(index - 1, total),
                total
            ), "info")
        end
        task.wait(CONFIG.ACTUAL_DELETE_TICK)
    end

    local deadline = os.clock() + 30
    while pending > 0 and os.clock() < deadline do
        task.wait(0.05)
    end
    return serverDeleted, localOnly
end

function App.readShellOptions()
    return {
        thickness = UI.shellThicknessField:Number(
            CONFIG.MIN_PART_SIZE,
            5,
            CONFIG.DEFAULT_SHELL_THICKNESS
        ),
        plateSize = UI.shellPlateField:Number(
            CONFIG.MIN_SHELL_PLATE_SIZE,
            CONFIG.MAX_SHELL_PLATE_SIZE,
            CONFIG.DEFAULT_SHELL_PLATE_SIZE
        ),
        budget = math.floor(UI.shellBudgetField:Number(
            100,
            CONFIG.MAX_SHELL_BUDGET,
            CONFIG.DEFAULT_SHELL_BUDGET,
            true
        )),
    }
end

function App.buildShellFrames(params, options)
    local model = params.model
    local thickness = options.thickness
    local cellSize = math.max(CONFIG.MIN_PART_SIZE, options.plateSize)
    local budget = options.budget
    local attempt = options.attempt or 1
    local originPlate = options.originPlateSize or options.plateSize

    if model.shellTriangleOverflow then
        return nil, 0, string.format(
            "模型三角形超过外壳捕获上限 %d；请先在 Blender 减面，或缩小模型规模。",
            CONFIG.MAX_SHELL_TRIANGLES
        )
    end

    local triangleCount = model.shellTriangleCount or 0
    if triangleCount == 0 then
        return nil, 0, "模型没有可用于外壳的三角形。"
    end

    local autoAdjusted = cellSize > originPlate + 1e-6
    local vertices = model.vertices
    local triA = model.shellTriA
    local triB = model.shellTriB
    local triC = model.shellTriC
    local frames = {}
    local skipped = 0
    local overBudget = false
    local surfaceReach = cellSize * clamp(CONFIG.SHELL_SURFACE_REACH, 0.4, 1.2)

    local minOverlap = 1 + 0.22 / math.max(cellSize, CONFIG.MIN_PART_SIZE)
    local voxelOverlap = clamp(
        math.max(CONFIG.SHELL_VOXEL_OVERLAP, minOverlap),
        1,
        2.5
    )
    local maxCells = CONFIG.SHELL_MAX_CELLS_PER_TRIANGLE
    local bevelCos = math.cos(math.rad(CONFIG.SHELL_BEVEL_ANGLE))
    local cellMap = {}
    local cellCount = 0
    local edgeMap = {}

    local signedVolume = 0
    for volumeIndex = 1, triangleCount do
        local ia = triA[volumeIndex] * 3
        local ib = triB[volumeIndex] * 3
        local ic = triC[volumeIndex] * 3
        local ax, ay, az = vertices[ia - 2], vertices[ia - 1], vertices[ia]
        local bx, by, bz = vertices[ib - 2], vertices[ib - 1], vertices[ib]
        local cx, cy, cz = vertices[ic - 2], vertices[ic - 1], vertices[ic]
        signedVolume = signedVolume
            + ax * (by * cz - bz * cy)
            - ay * (bx * cz - bz * cx)
            + az * (bx * cy - by * cx)
    end
    local flipNormals = signedVolume < 0

    local function planeBasisOf(normal)
        local ax, ay, az = math.abs(normal.X), math.abs(normal.Y), math.abs(normal.Z)
        local reference
        if ax <= ay and ax <= az then
            reference = Vector3.new(1, 0, 0)
        elseif ay <= az then
            reference = Vector3.new(0, 1, 0)
        else
            reference = Vector3.new(0, 0, 1)
        end
        local u = reference - normal * reference:Dot(normal)
        local magnitude = u.Magnitude
        if magnitude < 1e-6 then
            return nil, nil
        end
        u = u / magnitude
        return u, normal:Cross(u)
    end

    local function closestOnTriangle(px, py, pz, ax, ay, az, bx, by, bz, cx, cy, cz)
        local abx, aby, abz = bx - ax, by - ay, bz - az
        local acx, acy, acz = cx - ax, cy - ay, cz - az
        local apx, apy, apz = px - ax, py - ay, pz - az
        local d1 = abx * apx + aby * apy + abz * apz
        local d2 = acx * apx + acy * apy + acz * apz
        if d1 <= 0 and d2 <= 0 then
            return ax, ay, az
        end

        local bpx, bpy, bpz = px - bx, py - by, pz - bz
        local d3 = abx * bpx + aby * bpy + abz * bpz
        local d4 = acx * bpx + acy * bpy + acz * bpz
        if d3 >= 0 and d4 <= d3 then
            return bx, by, bz
        end

        local vc = d1 * d4 - d3 * d2
        if vc <= 0 and d1 >= 0 and d3 <= 0 then
            local denom = d1 - d3
            if math.abs(denom) < 1e-12 then
                return ax, ay, az
            end
            local t = d1 / denom
            return ax + abx * t, ay + aby * t, az + abz * t
        end

        local cpx, cpy, cpz = px - cx, py - cy, pz - cz
        local d5 = abx * cpx + aby * cpy + abz * cpz
        local d6 = acx * cpx + acy * cpy + acz * cpz
        if d6 >= 0 and d5 <= d6 then
            return cx, cy, cz
        end

        local vb = d5 * d2 - d1 * d6
        if vb <= 0 and d2 >= 0 and d6 <= 0 then
            local denom = d2 - d6
            if math.abs(denom) < 1e-12 then
                return ax, ay, az
            end
            local t = d2 / denom
            return ax + acx * t, ay + acy * t, az + acz * t
        end

        local va = d3 * d6 - d5 * d4
        if va <= 0 and (d4 - d3) >= 0 and (d5 - d6) >= 0 then
            local denom = (d4 - d3) + (d5 - d6)
            if math.abs(denom) < 1e-12 then
                return bx, by, bz
            end
            local t = (d4 - d3) / denom
            return bx + (cx - bx) * t, by + (cy - by) * t, bz + (cz - bz) * t
        end

        local denom = va + vb + vc
        if math.abs(denom) < 1e-12 then
            return ax, ay, az
        end
        local inv = 1 / denom
        local v = vb * inv
        local w = vc * inv
        return ax + abx * v + acx * w,
            ay + aby * v + acy * w,
            az + abz * v + acz * w
    end

    local function addEdge(aIndex, bIndex, ax, ay, az, bx, by, bz, nx, ny, nz)
        local lo, hi = aIndex, bIndex
        if lo > hi then
            lo, hi = hi, lo
        end
        local key = lo .. ":" .. hi
        local edge = edgeMap[key]
        if not edge then
            edgeMap[key] = {
                ax = ax, ay = ay, az = az,
                bx = bx, by = by, bz = bz,
                nx = nx, ny = ny, nz = nz,
                count = 1,
            }
        else
            edge.count = edge.count + 1
            if edge.count == 2 then
                edge.n2x, edge.n2y, edge.n2z = nx, ny, nz
            end
        end
    end

    local function addCell(ix, iy, iz, px, py, pz, nx, ny, nz, distance)
        local key = ix .. ":" .. iy .. ":" .. iz
        local cell = cellMap[key]
        if not cell then
            cellMap[key] = {
                px = px, py = py, pz = pz,
                nx = nx, ny = ny, nz = nz,
                count = 1,
                distance = distance,
            }
            cellCount = cellCount + 1
            if cellCount > budget then
                return false
            end
        else
            local dot = cell.nx * nx + cell.ny * ny + cell.nz * nz
            if dot >= 0 then
                cell.px = cell.px + px
                cell.py = cell.py + py
                cell.pz = cell.pz + pz
                cell.nx = cell.nx + nx
                cell.ny = cell.ny + ny
                cell.nz = cell.nz + nz
                cell.count = cell.count + 1
                if distance < cell.distance then
                    cell.distance = distance
                end
            elseif distance < cell.distance - 1e-6 then
                cell.px, cell.py, cell.pz = px, py, pz
                cell.nx, cell.ny, cell.nz = nx, ny, nz
                cell.count = 1
                cell.distance = distance
            end
        end
        return true
    end

    local maxRasterDepth = 4
    local function rasterizeTriangle(ax, ay, az, bx, by, bz, cx, cy, cz, nx, ny, nz, depth)
        local minX = math.floor((math.min(ax, bx, cx) - surfaceReach) / cellSize)
        local maxX = math.floor((math.max(ax, bx, cx) + surfaceReach) / cellSize)
        local minY = math.floor((math.min(ay, by, cy) - surfaceReach) / cellSize)
        local maxY = math.floor((math.max(ay, by, cy) + surfaceReach) / cellSize)
        local minZ = math.floor((math.min(az, bz, cz) - surfaceReach) / cellSize)
        local maxZ = math.floor((math.max(az, bz, cz) + surfaceReach) / cellSize)
        local countX = maxX - minX + 1
        local countY = maxY - minY + 1
        local countZ = maxZ - minZ + 1
        local cellTotal = countX * countY * countZ

        if cellTotal > maxCells and depth < maxRasterDepth then
            local abx, aby, abz = (ax + bx) * 0.5, (ay + by) * 0.5, (az + bz) * 0.5
            local bcx, bcy, bcz = (bx + cx) * 0.5, (by + cy) * 0.5, (bz + cz) * 0.5
            local cax, cay, caz = (cx + ax) * 0.5, (cy + ay) * 0.5, (cz + az) * 0.5
            rasterizeTriangle(ax, ay, az, abx, aby, abz, cax, cay, caz, nx, ny, nz, depth + 1)
            rasterizeTriangle(abx, aby, abz, bx, by, bz, bcx, bcy, bcz, nx, ny, nz, depth + 1)
            rasterizeTriangle(cax, cay, caz, bcx, bcy, bcz, cx, cy, cz, nx, ny, nz, depth + 1)
            rasterizeTriangle(abx, aby, abz, bcx, bcy, bcz, cax, cay, caz, nx, ny, nz, depth + 1)
            return
        end
        if cellTotal > maxCells then
            skipped = skipped + 1
            return
        end

        for ix = minX, maxX do
            if overBudget then
                return
            end
            local px = (ix + 0.5) * cellSize
            for iy = minY, maxY do
                local py = (iy + 0.5) * cellSize
                for iz = minZ, maxZ do
                    local pz = (iz + 0.5) * cellSize
                    local qx, qy, qz = closestOnTriangle(
                        px, py, pz,
                        ax, ay, az,
                        bx, by, bz,
                        cx, cy, cz
                    )
                    local dx, dy, dz = px - qx, py - qy, pz - qz
                    local distanceSq = dx * dx + dy * dy + dz * dz
                    local signedDistance = dx * nx + dy * ny + dz * nz
                    if math.abs(signedDistance) <= surfaceReach
                        and distanceSq <= surfaceReach * surfaceReach
                    then
                        if not addCell(ix, iy, iz, qx, qy, qz, nx, ny, nz, math.sqrt(distanceSq)) then
                            overBudget = true
                            return
                        end
                    end
                end
            end
        end
    end

    for triangleIndex = 1, triangleCount do
        if overBudget then
            break
        end
        if triangleIndex % 256 == 0 then
            if State.cancelRequested then
                return nil, skipped, "已取消实际建造。"
            end
            if triangleIndex % 2048 == 0 then
                task.wait()
            end
        end

        local ia = triA[triangleIndex] * 3
        local ib = triB[triangleIndex] * 3
        local ic = triC[triangleIndex] * 3
        local ax, ay, az = vertices[ia - 2], vertices[ia - 1], vertices[ia]
        local bx, by, bz = vertices[ib - 2], vertices[ib - 1], vertices[ib]
        local cx, cy, cz = vertices[ic - 2], vertices[ic - 1], vertices[ic]
        local pointA = params.transformPoint(ax, ay, az)
        local pointB = params.transformPoint(bx, by, bz)
        local pointC = params.transformPoint(cx, cy, cz)
        local cross = (pointB - pointA):Cross(pointC - pointA)
        if cross.Magnitude * 0.5 > 1e-9 then
            local normal = cross.Unit
            if flipNormals then
                normal = normal * -1
            end

            addEdge(
                triA[triangleIndex], triB[triangleIndex],
                pointA.X, pointA.Y, pointA.Z,
                pointB.X, pointB.Y, pointB.Z,
                normal.X, normal.Y, normal.Z
            )
            addEdge(
                triB[triangleIndex], triC[triangleIndex],
                pointB.X, pointB.Y, pointB.Z,
                pointC.X, pointC.Y, pointC.Z,
                normal.X, normal.Y, normal.Z
            )
            addEdge(
                triC[triangleIndex], triA[triangleIndex],
                pointC.X, pointC.Y, pointC.Z,
                pointA.X, pointA.Y, pointA.Z,
                normal.X, normal.Y, normal.Z
            )

            rasterizeTriangle(
                pointA.X, pointA.Y, pointA.Z,
                pointB.X, pointB.Y, pointB.Z,
                pointC.X, pointC.Y, pointC.Z,
                normal.X, normal.Y, normal.Z,
                0
            )
        else
            skipped = skipped + 1
        end
    end

    if State.cancelRequested then
        return nil, skipped, "已取消实际建造。"
    end

    if overBudget then
        if cellSize < CONFIG.MAX_SHELL_PLATE_SIZE - 1e-6 and attempt < 12 then
            local nextSize = math.min(CONFIG.MAX_SHELL_PLATE_SIZE, cellSize * 1.5)
            App.status(string.format(
                "外壳超出预算，体素尺寸 %.2f→%.2f 后重试 ...",
                cellSize,
                nextSize
            ), "warn")
            return App.buildShellFrames(params, {
                thickness = thickness,
                plateSize = nextSize,
                budget = budget,
                attempt = attempt + 1,
                originPlateSize = originPlate,
            })
        end
        return nil, skipped, string.format(
            "外壳体素仍超过最大积木数 %d（体素 %.2f，上限 %.2f）；请减面或提高预算。",
            budget,
            cellSize,
            CONFIG.MAX_SHELL_PLATE_SIZE
        )
    end

    if cellCount == 0 then
        return nil, skipped, "没有可生成的外壳体素；三角形可能过小或过大。"
    end

    for _, cell in pairs(cellMap) do
        local count = math.max(1, cell.count)
        local nx, ny, nz = cell.nx / count, cell.ny / count, cell.nz / count
        local magnitude = math.sqrt(nx * nx + ny * ny + nz * nz)
        if magnitude > 1e-6 then
            nx, ny, nz = nx / magnitude, ny / magnitude, nz / magnitude
            local u, v = planeBasisOf(Vector3.new(nx, ny, nz))
            if u then
                local px, py, pz = cell.px / count, cell.py / count, cell.pz / count
                local frameSize = cellSize * voxelOverlap
                frames[#frames + 1] = {
                    cframe = CFrame.fromMatrix(
                        Vector3.new(
                            px - nx * (thickness * 0.5),
                            py - ny * (thickness * 0.5),
                            pz - nz * (thickness * 0.5)
                        ),
                        u,
                        v,
                        Vector3.new(nx, ny, nz)
                    ),
                    size = Vector3.new(frameSize, frameSize, thickness),
                }
            end
        end
    end

    if #frames == 0 then
        return nil, skipped, "没有可生成的外壳体素；三角形可能过小或过大。"
    end

    local bevelAdded = 0
    if CONFIG.SHELL_BEVEL_ENABLED then
        local bevelWidth = cellSize * CONFIG.SHELL_BEVEL_WIDTH
        local segmentLength = math.max(CONFIG.SHELL_BEVEL_SEGMENT, cellSize)
        for _, edge in pairs(edgeMap) do
            if #frames >= budget then
                break
            end
            if edge.count == 2 and edge.n2x then
                local dot = edge.nx * edge.n2x + edge.ny * edge.n2y + edge.nz * edge.n2z
                if dot < bevelCos then
                    local sumX = edge.nx + edge.n2x
                    local sumY = edge.ny + edge.n2y
                    local sumZ = edge.nz + edge.n2z
                    local sumMagnitude = math.sqrt(sumX * sumX + sumY * sumY + sumZ * sumZ)
                    if sumMagnitude > 1e-6 then
                        local nx, ny, nz = sumX / sumMagnitude, sumY / sumMagnitude, sumZ / sumMagnitude
                        local ax, ay, az = edge.ax, edge.ay, edge.az
                        local dirX, dirY, dirZ = edge.bx - ax, edge.by - ay, edge.bz - az
                        local length = math.sqrt(dirX * dirX + dirY * dirY + dirZ * dirZ)
                        if length > 1e-6 then
                            dirX, dirY, dirZ = dirX / length, dirY / length, dirZ / length
                            local segments = math.max(1, math.ceil(length / segmentLength))
                            local actualLength = length / segments
                            local tangentX = ny * dirZ - nz * dirY
                            local tangentY = nz * dirX - nx * dirZ
                            local tangentZ = nx * dirY - ny * dirX
                            local tangentMagnitude = math.sqrt(
                                tangentX * tangentX + tangentY * tangentY + tangentZ * tangentZ
                            )
                            if tangentMagnitude > 1e-6 then
                                tangentX = tangentX / tangentMagnitude
                                tangentY = tangentY / tangentMagnitude
                                tangentZ = tangentZ / tangentMagnitude
                                for segment = 0, segments - 1 do
                                    if #frames >= budget then
                                        break
                                    end
                                    local offset = (segment + 0.5) * actualLength
                                    local centerX = ax + dirX * offset + nx * (thickness * 0.5)
                                    local centerY = ay + dirY * offset + ny * (thickness * 0.5)
                                    local centerZ = az + dirZ * offset + nz * (thickness * 0.5)
                                    frames[#frames + 1] = {
                                        cframe = CFrame.fromMatrix(
                                            Vector3.new(centerX, centerY, centerZ),
                                            Vector3.new(dirX, dirY, dirZ),
                                            Vector3.new(tangentX, tangentY, tangentZ),
                                            Vector3.new(nx, ny, nz)
                                        ),
                                        size = Vector3.new(actualLength * 1.04, bevelWidth, thickness),
                                    }
                                    bevelAdded = bevelAdded + 1
                                end
                            end
                        end
                    end
                end
            end
        end
    end

    local autoText = ""
    if autoAdjusted then
        autoText = string.format("预算不足，体素尺寸自动 %.2f→%.2f；", originPlate, cellSize)
    end
    return frames, skipped, string.format(
        "%s全局体素壳：%d 三角形 → %d 块（%d 格 + %d 倒角，格子 %.2f）",
        autoText,
        triangleCount,
        #frames,
        cellCount,
        bevelAdded,
        cellSize
    )
end

function App.buildWireframeFrames(params)
    local render, renderError, simplifyInfo = App.prepareRender(params.maxEdges, function(alpha)
        App.setProgress(alpha * 0.2)
        App.status(string.format("准备实际建造网格 ... %d%%", math.floor(alpha * 100)), "info")
    end)
    if not render then
        return nil, 0, "实际建造准备失败：" .. tostring(renderError)
    end
    if State.cancelRequested then
        return nil, 0, "已取消实际建造。"
    end

    local frames = {}
    local skipped = 0
    for edgeIndex = 1, render.count do
        local pointA = params.transformPoint(
            render.ax[edgeIndex],
            render.ay[edgeIndex],
            render.az[edgeIndex]
        )
        local pointB = params.transformPoint(
            render.bx[edgeIndex],
            render.by[edgeIndex],
            render.bz[edgeIndex]
        )
        local dx = pointB.X - pointA.X
        local dy = pointB.Y - pointA.Y
        local dz = pointB.Z - pointA.Z
        local length = math.sqrt(dx * dx + dy * dy + dz * dz)
        if length > 1e-6 and length <= CONFIG.MAX_PART_LENGTH then
            local middle = Vector3.new(
                (pointA.X + pointB.X) * 0.5,
                (pointA.Y + pointB.Y) * 0.5,
                (pointA.Z + pointB.Z) * 0.5
            )
            local direction = Vector3.new(dx / length, dy / length, dz / length)
            frames[#frames + 1] = {
                cframe = CFrame.lookAt(middle, middle + direction),
                size = Vector3.new(
                    params.thickness,
                    params.thickness,
                    math.max(
                        math.min(length + params.thickness, CONFIG.MAX_PART_LENGTH),
                        params.thickness
                    )
                ),
                length = length,
            }
        else
            skipped = skipped + 1
        end
    end

    local detail = ""
    if simplifyInfo then
        detail = string.format("简化 %d → %d 边", simplifyInfo.sourceEdgeCount, simplifyInfo.count)
    end
    return frames, skipped, detail
end

function App.prepareActualFrames(params, shellMode)
    if not shellMode then
        return App.buildWireframeFrames(params)
    end
    return App.buildShellFrames(params, App.readShellOptions())
end

function App.startActualBuild(shellMode)
    if State.actualBuilding or State.generating or State.parsing then
        App.status("正在" .. tostring(busyReason()) .. "，请等待或先取消。", "warn")
        return
    end
    if not State.model then
        App.status("请先导入 OBJ。", "error")
        return
    end
    if State.previewVisible then
        App.clearPreview(false)
    end
    if State.needsReparse and State.sourceText then
        if not App.importFromText(State.sourceText, State.sourceName) then
            return
        end
    end

    local params, paramsError = App.readTransformParams()
    if not params then
        App.status(paramsError, "error")
        return
    end

    local model = State.model
    if not shellMode and model.edgeCount > params.maxEdges and not UI.autoSimplifyToggle:Value() then
        App.status(string.format(
            "模型有 %d 条边，超过上限 %d；请提高上限，或打开自动简化。",
            model.edgeCount,
            params.maxEdges
        ), "error")
        return
    end

    local folder = App.getPlayerBlockFolder()
    if not folder then
        App.status("找不到 Workspace.Blocks/<玩家名>；确认已进入游戏并拥有建造区。", "error")
        return
    end
    if not App.findTool(CONFIG.ACTUAL_TOOL_BUILD) then
        App.status("缺少 BuildingTool，无法放置 PlasticBlock。", "error")
        return
    end
    if not App.findTool(CONFIG.ACTUAL_TOOL_SCALE) then
        App.status("缺少 ScalingTool，无法缩放 / 旋转实际积木。", "error")
        return
    end
    local buildingParts = ReplicatedStorage:FindFirstChild("BuildingParts")
    if not buildingParts or not buildingParts:FindFirstChild(CONFIG.ACTUAL_BLOCK_NAME) then
        App.status("ReplicatedStorage.BuildingParts.PlasticBlock 不存在，无法实际建造。", "error")
        return
    end

    local existingBlocks = #folder:GetChildren()
    if shellMode and existingBlocks >= CONFIG.ACTUAL_CONFIRM_BLOCK_THRESHOLD and not State.buildArmed then
        State.buildArmed = true
        print(string.format("[OBJ Wireframe] 建造区已有 %d 块", existingBlocks))
        App.status(string.format(
            "建造区已有 %d 块，它们会和这次一起占用额度。建议先「清空建造区」（连点两次）；"
                .. "确实要叠加，请在 %d 秒内再点一次本按钮。",
            existingBlocks,
            CONFIG.ACTUAL_ARM_SECONDS
        ), "warn")
        task.delay(CONFIG.ACTUAL_ARM_SECONDS, function()
            State.buildArmed = false
        end)
        return
    end
    State.buildArmed = false

    local blockID = App.getPlasticBlockID()
    local buildStart = os.clock()
    local previousActualBlocks = State.actualBlocks
    State.actualBlocks = {}
    State.actualBuilding = true
    State.cancelRequested = false
    State.actualBuildToken = State.actualBuildToken + 1
    local token = State.actualBuildToken
    App.setProgress(0)
    App.status(shellMode and "准备完整模型外壳数据 ..." or "准备实际建造数据 ...", "info")
    task.wait()

    local frames, skipped, framesDetail = App.prepareActualFrames(params, shellMode)
    if token ~= State.actualBuildToken then
        State.actualBuilding = false
        State.actualBlocks = previousActualBlocks
        return
    end
    if not frames then
        State.actualBuilding = false
        State.cancelRequested = false
        State.actualBlocks = previousActualBlocks
        App.setProgress(0)
        App.status(framesDetail or "实际建造准备失败。", framesDetail == "已取消实际建造。" and "warn" or "error")
        return
    end
    if State.cancelRequested then
        State.actualBuilding = false
        State.cancelRequested = false
        State.actualBlocks = previousActualBlocks
        App.setProgress(0)
        App.status("已取消实际建造。", "warn")
        return
    end

    local total = #frames
    if total == 0 then
        State.actualBuilding = false
        State.actualBlocks = previousActualBlocks
        App.setProgress(0)
        App.status(shellMode and "没有可生成的外壳板。" or "没有可实际建造的有效边。", "error")
        return
    end

    if total > 3000 then
        App.status(string.format("目标 %d 块，可能耗时较长；随时可点「取消」。", total), "warn")
    end

    local before = {}
    for _, child in ipairs(folder:GetChildren()) do
        before[child] = true
    end

    local newBlocks = {}
    local leftovers = {}
    local arrivalConnection = nil

    local arrivedCount = 0
    arrivalConnection = folder.ChildAdded:Connect(function(child)
        if not before[child] then
            arrivedCount = arrivedCount + 1
        end
    end)

    local function disconnectArrival()
        if arrivalConnection then
            pcall(function()
                arrivalConnection:Disconnect()
            end)
            arrivalConnection = nil
        end
    end

    local function abortActual(message, kind)
        State.actualBuilding = false
        State.cancelRequested = false
        App.setProgress(0)
        disconnectArrival()
        if #newBlocks > 0 then
            local serverDeleted, localOnly = App.deleteModelsWithTool(newBlocks)
            if localOnly > 0 and serverDeleted == 0 then
                message = message .. "（部分暂存块可能仍留在服务器）"
            end
        end
        State.actualBlocks = previousActualBlocks
        App.status(message, kind)
    end

    local buildTool = App.equipTool(CONFIG.ACTUAL_TOOL_BUILD)
    local buildInvoke = buildTool and buildTool:FindFirstChild("RF")
    if not buildInvoke or not buildInvoke:IsA("RemoteFunction") then
        abortActual("BuildingTool 上没有可用的 RF RemoteFunction。", "error")
        return
    end

    local stageGap = CONFIG.ACTUAL_STAGE_GAP
    local stageCols = CONFIG.ACTUAL_STAGE_COLS
    local stageSpan = stageCols * stageCols
    local stageOrigin = params.worldPosition
    local layerStride = math.ceil(total / stageSpan) + 1

    local function stageSlotOf(slotIndex, layerPass)
        local zero = slotIndex - 1
        local col = zero % stageCols
        local row = math.floor(zero / stageCols) % stageCols
        local layer = (layerPass or 0) * layerStride + math.floor(zero / stageSpan)
        return col, row, layer
    end

    local function stagingCFrameOf(slotIndex, layerPass)
        local col, row, layer = stageSlotOf(slotIndex, layerPass)
        return CFrame.new(
            stageOrigin.X + col * stageGap,
            CONFIG.ACTUAL_STAGE_Y + layer * stageGap,
            stageOrigin.Z + row * stageGap
        )
    end

    local placePending = 0
    local placeSubmitted = 0
    local placeFailed = 0
    local placePeakPending = 0
    local placeReturns = {}

    local function notePlaceReturn(ok, result)
        local key
        if ok then
            if type(result) == "table" or type(result) == "userdata" then
                key = tostring(result):gsub("%s+", " ")
            else
                key = tostring(result)
            end
        else
            key = "异常: " .. tostring(result)
        end
        placeReturns[key] = (placeReturns[key] or 0) + 1
    end

    local function placeBlock(slotIndex, layerPass)
        local stagingCFrame = stagingCFrameOf(slotIndex, layerPass)
        placePending = placePending + 1
        placeSubmitted = placeSubmitted + 1
        if placePending > placePeakPending then
            placePeakPending = placePending
        end
        task.spawn(function()
            local ok, result = pcall(function()
                return buildInvoke:InvokeServer(
                    CONFIG.ACTUAL_BLOCK_NAME,
                    blockID,
                    nil,
                    nil,
                    true,
                    stagingCFrame,
                    nil,
                    false
                )
            end)
            notePlaceReturn(ok, result)
            if not ok then
                placeFailed = placeFailed + 1
            end
            placePending = placePending - 1
        end)
    end

    local function ensureToolInvoke(toolName, currentInvoke)
        local character = LocalPlayer.Character
        if not character then
            return currentInvoke
        end
        local equipped = character:FindFirstChild(toolName)
        if equipped and equipped:IsA("Tool") then
            local invoke = equipped:FindFirstChild("RF")
            if invoke and invoke:IsA("RemoteFunction") then
                return invoke
            end
        end
        local tool = App.equipTool(toolName)
        local invoke = tool and tool:FindFirstChild("RF")
        if invoke and invoke:IsA("RemoteFunction") then
            return invoke
        end
        return nil
    end

    local function submitPlacements(slotList, layerPass, baseProgress)
        local cursor = 1
        local slotCount = #slotList
        local batchSize = math.max(1, CONFIG.ACTUAL_PLACE_BATCH)
        local batchWait = CONFIG.ACTUAL_PLACE_BATCH_WAIT

        while cursor <= slotCount do
            if State.cancelRequested or token ~= State.actualBuildToken then
                return "cancelled"
            end

            local batchEnd = math.min(slotCount, cursor + batchSize - 1)
            for index = cursor, batchEnd do
                placeBlock(slotList[index], layerPass)
            end
            cursor = batchEnd + 1

            App.setProgress(baseProgress + 0.2 * ((cursor - 1) / slotCount))
            App.status(string.format(
                "放置暂存块 ... 已提交 %d / %d（%d 块/批，批间 %.2f 秒）",
                cursor - 1,
                slotCount,
                batchSize,
                batchWait
            ), "info")

            task.wait(batchWait)
        end
        return "ok"
    end

    local function drainPlacements(timeout, label)
        local deadline = os.clock() + timeout
        local cancelDeadline = nil
        while placePending > 0 and os.clock() < deadline do
            if State.cancelRequested then
                cancelDeadline = cancelDeadline or (os.clock() + 2)
                if os.clock() > cancelDeadline then
                    break
                end
            end
            App.status(string.format(
                "%s：等待服务器确认 ... 在途 %d 块",
                label or "放置",
                placePending
            ), "info")
            task.wait(0.05)
        end
        return placePending == 0
    end

    local scannedSet = {}
    local function scanNewBlocks()
        local list = {}
        for _, child in ipairs(folder:GetChildren()) do
            if not before[child] and child:IsA("Model") and child.PrimaryPart then
                list[#list + 1] = child
            end
        end
        return list
    end

    local function absorbScanned(list)
        for _, block in ipairs(list) do
            if not scannedSet[block] then
                scannedSet[block] = true
                newBlocks[#newBlocks + 1] = block
            end
        end
    end

    local function scanUntilSettled(expected, timeout)
        local deadline = os.clock() + timeout
        local list = scanNewBlocks()
        local stable = 0
        while os.clock() < deadline do
            if #list >= expected or State.cancelRequested then
                return list
            end
            task.wait(0.2)
            local nextList = scanNewBlocks()
            if #nextList == #list then
                stable = stable + 1
                if stable >= 3 then
                    return nextList
                end
            else
                stable = 0
            end
            list = nextList
        end
        return list
    end

    local matched = {}
    local used = {}
    local scannedAll = {}

    local function matchSlots(slotList, layerPass)
        local byLayer = {}
        for _, block in ipairs(scannedAll) do
            local part = block.PrimaryPart
            if part and not used[block] then
                local layer = math.floor(
                    (part.Position.Y - CONFIG.ACTUAL_STAGE_Y) / stageGap + 0.5
                )
                byLayer[layer] = byLayer[layer] or {}
                byLayer[layer][#byLayer[layer] + 1] = block
            end
        end

        local count = 0
        local tolerance = math.max(CONFIG.ACTUAL_MATCH_TOLERANCE, stageGap * 0.45)
        for _, slotIndex in ipairs(slotList) do
            if not matched[slotIndex] then
                local _, _, layer = stageSlotOf(slotIndex, layerPass)
                local target = stagingCFrameOf(slotIndex, layerPass).Position
                local best
                local bestDistance
                for deltaLayer = -2, 2 do
                    local bucket = byLayer[layer + deltaLayer]
                    if bucket then
                        for _, block in ipairs(bucket) do
                            if not used[block] then
                                local distance = math.abs(block.PrimaryPart.Position.Y - target.Y)
                                if distance <= tolerance
                                    and (not bestDistance or distance < bestDistance)
                                then
                                    best = block
                                    bestDistance = distance
                                end
                            end
                        end
                    end
                end
                if best then
                    used[best] = true
                    matched[slotIndex] = best
                    count = count + 1
                end
            end
        end
        return count
    end

    local function finishCancelled()
        absorbScanned(scanNewBlocks())
        abortActual("已取消实际建造。", "warn")
    end

    local settleBudget = math.max(8, 4 + total * 0.02)
    local scanBudget = math.max(6, 2 + total * 0.012)

    local firstPass = {}
    for slotIndex = 1, total do
        firstPass[slotIndex] = slotIndex
    end

    local submitResult = submitPlacements(firstPass, 0, 0.2)
    if submitResult == "cancelled" then
        finishCancelled()
        return
    end

    drainPlacements(settleBudget, "放置")
    if State.cancelRequested or token ~= State.actualBuildToken then
        finishCancelled()
        return
    end

    scannedAll = scanUntilSettled(total, scanBudget)
    absorbScanned(scannedAll)
    matchSlots(firstPass, 0)

    local pendingSlots = {}
    for slotIndex = 1, total do
        if not matched[slotIndex] then
            pendingSlots[#pendingSlots + 1] = slotIndex
        end
    end

    local maxRetryPasses = shellMode and CONFIG.ACTUAL_RETRY_PASSES or 0
    local pass = 0
    while #pendingSlots > 0 and pass < maxRetryPasses do
        pass = pass + 1
        if State.cancelRequested or token ~= State.actualBuildToken then
            finishCancelled()
            return
        end
        App.status(string.format("%d 块未到位，开始第 %d 次补建 ...", #pendingSlots, pass), "warn")
        local retryResult = submitPlacements(pendingSlots, pass, 0.2)
        if retryResult == "cancelled" then
            finishCancelled()
            return
        end
        drainPlacements(settleBudget, "补建")
        if State.cancelRequested then
            finishCancelled()
            return
        end
        scannedAll = scanUntilSettled(#scannedAll + #pendingSlots, scanBudget)
        absorbScanned(scannedAll)
        matchSlots(pendingSlots, pass)
        local stillMissing = {}
        for _, slotIndex in ipairs(pendingSlots) do
            if not matched[slotIndex] then
                stillMissing[#stillMissing + 1] = slotIndex
            end
        end
        pendingSlots = stillMissing
    end

    local matchedCount = total - #pendingSlots
    if matchedCount == 0 then
        abortActual("无法把暂存块和模型位置对上；未执行缩放。", "error")
        return
    end

    for _, block in ipairs(scannedAll) do
        if not used[block] then
            leftovers[#leftovers + 1] = block
        end
    end

    local scaleTool = App.equipTool(CONFIG.ACTUAL_TOOL_SCALE)
    local scaleInvoke = scaleTool and scaleTool:FindFirstChild("RF")
    if not scaleInvoke or not scaleInvoke:IsA("RemoteFunction") then
        abortActual("ScalingTool 上没有可用的 RF RemoteFunction。", "error")
        return
    end

    local scaleSlots = {}
    for slotIndex = 1, total do
        if matched[slotIndex] then
            scaleSlots[#scaleSlots + 1] = slotIndex
        end
    end

    local scaled = 0
    local scaleFailed = 0
    local acceptScaleResults = true
    local pending = 0
    local scaleCursor = 1
    local scaleMaxInFlight = CONFIG.ACTUAL_SCALE_MAX_IN_FLIGHT
    local scaleRate = CONFIG.ACTUAL_SCALE_RATE
    local scaleWindowStart = os.clock()
    local scaleWindowSent = 0
    local scalePassStart = os.clock()
    local scaleNextStatus = scalePassStart
    local scaleNextToolCheck = scalePassStart + 1

    while scaleCursor <= #scaleSlots do
        if State.cancelRequested or token ~= State.actualBuildToken then
            break
        end
        local now = os.clock()
        if now - scaleWindowStart >= 1 then
            scaleWindowStart = now
            scaleWindowSent = 0
        end
        if now >= scaleNextToolCheck then
            scaleNextToolCheck = now + 1
            scaleInvoke = ensureToolInvoke(CONFIG.ACTUAL_TOOL_SCALE, scaleInvoke) or scaleInvoke
        end

        local burst = 0
        while scaleCursor <= #scaleSlots
            and pending < scaleMaxInFlight
            and scaleWindowSent < scaleRate
        do
            local slotIndex = scaleSlots[scaleCursor]
            local block = matched[slotIndex]
            local frame = frames[slotIndex]
            if block and frame then
                pending = pending + 1
                scaleWindowSent = scaleWindowSent + 1
                task.spawn(function()
                    local ok = App.applyScale(scaleInvoke, block, frame)
                    if acceptScaleResults then
                        if ok and block.Parent and block.PrimaryPart then
                            scaled = scaled + 1
                        else
                            scaleFailed = scaleFailed + 1
                            leftovers[#leftovers + 1] = block
                        end
                    end
                    pending = pending - 1
                end)
            end
            scaleCursor = scaleCursor + 1
            burst = burst + 1
            if burst >= 250 then
                break
            end
        end

        App.setProgress(0.4 + 0.45 * ((scaleCursor - 1) / #scaleSlots))
        if now >= scaleNextStatus then
            scaleNextStatus = now + 0.3
            local elapsed = math.max(0.5, now - scalePassStart)
            local returned = scaled + scaleFailed
            local rate = returned / elapsed
            local remaining = #scaleSlots - (scaleCursor - 1) + pending
            local etaText = ""
            if rate > 0.5 and remaining > 0 then
                local eta = remaining / rate
                if eta > 600 then
                    etaText = string.format("，预计还要 %.0f 分钟", eta / 60)
                else
                    etaText = string.format("，约剩 %d 秒", math.floor(eta))
                end
            end
            App.status(string.format(
                "缩放 / 旋转 ... 提交 %d / %d，已返回 %d，%.0f 块/秒%s",
                scaleCursor - 1,
                #scaleSlots,
                returned,
                rate,
                etaText
            ), "info")
        end
        task.wait(CONFIG.ACTUAL_SCALE_TICK)
    end

    local settleDeadline = os.clock() + math.max(6, 2 + total * 0.01)
    while pending > 0 and os.clock() < settleDeadline and not State.cancelRequested do
        App.status(string.format("等待服务器确认缩放 ... 在途 %d 块", pending), "info")
        task.wait(0.05)
    end
    if State.cancelRequested or token ~= State.actualBuildToken then
        acceptScaleResults = false
    elseif pending > 0 then
        acceptScaleResults = false
        App.status(string.format("还有 %d 个缩放请求没返回，先按当前状态分类 ...", pending), "warn")
    end

    local verifyTolerance = CONFIG.ACTUAL_VERIFY_TOLERANCE
    local stagedCeiling = CONFIG.ACTUAL_STAGE_Y - 3
    local canTellStaging = (params.worldPosition.Y + params.scaledMax + 5) < stagedCeiling

    local function isStuckAtStaging(block, frame)
        if not canTellStaging then
            return false
        end
        local part = block and block.PrimaryPart
        if not part then
            return false
        end
        return part.Position.Y >= stagedCeiling
            and (part.Position - frame.cframe.Position).Magnitude > verifyTolerance
    end

    local stuckPairs = {}
    for _, slotIndex in ipairs(scaleSlots) do
        local block = matched[slotIndex]
        local frame = frames[slotIndex]
        if block and isStuckAtStaging(block, frame) then
            stuckPairs[#stuckPairs + 1] = { block = block, frame = frame }
        end
    end

    if #stuckPairs > 0 and not State.cancelRequested and token == State.actualBuildToken then
        App.status(string.format("%d 块仍在暂存高度，重试一次缩放 ...", #stuckPairs), "warn")
        local retryPending = 0
        for _, pair in ipairs(stuckPairs) do
            retryPending = retryPending + 1
            task.spawn(function()
                App.applyScale(scaleInvoke, pair.block, pair.frame)
                retryPending = retryPending - 1
            end)
        end
        local retryDeadline = os.clock() + math.max(8, 3 + #stuckPairs * 0.03)
        while retryPending > 0 and os.clock() < retryDeadline and not State.cancelRequested do
            task.wait(0.05)
        end
        task.wait(0.6)
    end

    local offPosition = 0
    local stillStuck = 0
    for _, slotIndex in ipairs(scaleSlots) do
        local block = matched[slotIndex]
        local frame = frames[slotIndex]
        local part = block and block.PrimaryPart
        if not part then
            if block then
                leftovers[#leftovers + 1] = block
            end
        elseif isStuckAtStaging(block, frame) then
            stillStuck = stillStuck + 1
            leftovers[#leftovers + 1] = block
        else
            State.actualBlocks[#State.actualBlocks + 1] = block
            if (part.Position - frame.cframe.Position).Magnitude > verifyTolerance then
                offPosition = offPosition + 1
            end
        end
    end
    scaled = #State.actualBlocks

    disconnectArrival()

    do
        local entries = {}
        for key, count in pairs(placeReturns) do
            entries[#entries + 1] = { key = key, count = count }
        end
        table.sort(entries, function(a, b)
            return a.count > b.count
        end)
        local parts = {}
        for index = 1, math.min(#entries, 6) do
            parts[#parts + 1] = string.format("%s×%d", entries[index].key, entries[index].count)
        end
        print("[OBJ Wireframe] 放置返回: " .. (#parts > 0 and table.concat(parts, "  ") or "无"))
    end
    print(string.format(
        "[OBJ Wireframe] 建造统计：目标 %d，提交 %d，异常 %d，服务器生成 %d，匹配 %d，"
            .. "未匹配 %d，缩放失败 %d，仍在暂存 %d，位置偏差 %d，峰值在途 %d",
        total,
        placeSubmitted,
        placeFailed,
        arrivedCount,
        matchedCount,
        #pendingSlots,
        scaleFailed,
        stillStuck,
        offPosition,
        placePeakPending
    ))

    local wasCancelled = State.cancelRequested
    local tokenChanged = token ~= State.actualBuildToken
    State.actualBuilding = false
    State.cancelRequested = false

    if tokenChanged then
        State.actualBlocks = previousActualBlocks
        return
    end

    if wasCancelled then
        local serverDeleted, localOnly = App.deleteModelsWithTool(newBlocks)
        State.actualBlocks = previousActualBlocks
        App.setProgress(0)
        if localOnly > 0 and serverDeleted == 0 then
            App.status("已取消实际建造；本机已移除部分积木，但服务器上可能仍有暂存块。", "warn")
        else
            App.status(string.format(
                "已取消实际建造并清理：服务器删除 %d 块，本机兜底 %d 块。",
                serverDeleted,
                localOnly
            ), "warn")
        end
        return
    end

    if scaled == 0 then
        abortActual("所有积木缩放失败；已尽量清理暂存块。", "error")
        return
    end

    local leftoverServer, leftoverLocal = 0, 0
    if #leftovers > 0 then
        leftoverServer, leftoverLocal = App.deleteModelsWithTool(leftovers)
    end

    if previousActualBlocks and #previousActualBlocks > 0 then
        for _, block in ipairs(previousActualBlocks) do
            State.actualBlocks[#State.actualBlocks + 1] = block
        end
    end

    local details = string.format(
        shellMode and "完整模型外壳完成：建成 %d / %d 块" or "实际建造完成：建成 %d / %d 块",
        scaled,
        total
    )
    if #pendingSlots > 0 then
        details = details .. string.format(
            "；%d 块始终没生成（服务器拒收，通常是库存 / 上限 / 限流）",
            #pendingSlots
        )
        details = details .. "。先「清空建造区」清掉旧残块再重试（重载脚本后本按钮记不到旧块）"
        if scaled > 200 then
            details = details .. string.format(
                "；若清空后仍缺，把预算降到 %d 左右",
                math.floor(scaled * 0.9)
            )
        end
    end
    if framesDetail and framesDetail ~= "" then
        details = details .. "（" .. framesDetail .. "）"
    end
    if skipped > 0 then
        details = details .. string.format("，跳过 %d 个退化 / 超限三角形或边", skipped)
    end
    if placeFailed > 0 then
        details = details .. string.format("，放置异常 %d", placeFailed)
    end
    if scaleFailed > 0 then
        details = details .. string.format("，缩放异常 %d", scaleFailed)
    end
    if stillStuck > 0 then
        details = details .. string.format("，清理没被移动的暂存块 %d", stillStuck)
    end
    if offPosition > 0 then
        details = details .. string.format("，位置有偏差 %d（已保留）", offPosition)
    end
    if #leftovers > 0 then
        details = details .. string.format(
            "，清理残留 %d（服务器 %d / 本机 %d）",
            #leftovers,
            leftoverServer,
            leftoverLocal
        )
    end
    local areaCount = 0
    if folder and folder.Parent then
        areaCount = #folder:GetChildren()
    end
    details = details .. string.format(
        "；建造区现有 %d 块 · 耗时 %.1f 秒",
        areaCount,
        os.clock() - buildStart
    )

    App.setProgress(1)
    App.status(details .. "。", (#pendingSlots > 0 or stillStuck > 0) and "warn" or "ok")
end

function App.clearActualBuild()
    if State.actualBuilding then
        App.status("实际建造进行中；请先点「取消」。", "warn")
        return
    end
    local count = #State.actualBlocks
    if count == 0 then
        App.status("没有本脚本记录的积木；如需整体清理请用「清空建造区」。", "info")
        return
    end

    local models = State.actualBlocks
    State.actualBlocks = {}
    local serverDeleted, localOnly = App.deleteModelsWithTool(models)
    App.setProgress(0)
    if localOnly > 0 and serverDeleted == 0 then
        App.status(string.format(
            "已在本机移除 %d 块，但没有 DeleteTool / 远程删除，服务器上可能仍保留。",
            count
        ), "warn")
    else
        App.status(string.format(
            "已清除实际建造：服务器删除 %d 块，本机兜底 %d 块。",
            serverDeleted,
            localOnly
        ), "ok")
    end
end

function App.clearBuildArea()
    if isBusy() then
        App.status("正在" .. tostring(busyReason()) .. "，请先取消。", "warn")
        return
    end
    local folder = App.getPlayerBlockFolder()
    if not folder then
        App.status("找不到 Workspace.Blocks/<玩家名>。", "error")
        return
    end

    local models = {}
    for _, child in ipairs(folder:GetChildren()) do
        if child:IsA("Model") and child.PrimaryPart then
            models[#models + 1] = child
        end
    end
    if #models == 0 then
        State.clearAreaArmed = false
        App.status("建造区已经是空的。", "info")
        return
    end
    if not State.clearAreaArmed then
        State.clearAreaArmed = true
        App.status(string.format(
            "建造区有 %d 块；在 %d 秒内再点一次「清空建造区」确认全部删除。",
            #models,
            CONFIG.CLEAR_AREA_ARM_SECONDS
        ), "warn")
        task.delay(CONFIG.CLEAR_AREA_ARM_SECONDS, function()
            State.clearAreaArmed = false
        end)
        return
    end

    State.clearAreaArmed = false
    local serverDeleted, localOnly = App.deleteModelsWithTool(models)
    State.actualBlocks = {}
    App.setProgress(0)
    App.status(string.format(
        "建造区已清空：服务器删除 %d 块，本机兜底 %d 块。",
        serverDeleted,
        localOnly
    ), "ok")
end

local logModal = Kit.modal(modalGui, "LogModal", "运行日志（最近 150 条）", 760, 560)

local logList = Instance.new("ScrollingFrame")
logList.Name = "LogList"
logList.BackgroundColor3 = THEME.inset
logList.BorderSizePixel = 0
logList.Position = UDim2.fromOffset(12, 34)
logList.Size = UDim2.new(1, -24, 1, -86)
logList.ScrollBarThickness = 5
logList.ScrollBarImageColor3 = THEME.accent
logList.ScrollingDirection = Enum.ScrollingDirection.Y
logList.CanvasSize = UDim2.new(0, 0, 0, 0)
logList.AutomaticCanvasSize = Enum.AutomaticSize.Y
logList.Parent = logModal.Body
Kit.round(logList, 6)
Kit.outline(logList, THEME.line, 1, 0.5)
Kit.padding(logList, 6, 6, 6, 6)
Kit.vlist(logList, 3)

local logHint = Kit.label(
    logModal.Body,
    "完整历史也会同时输出到执行器控制台（print / warn）。",
    { size = 11, color = THEME.textDim }
)
logHint.Position = UDim2.fromOffset(12, 10)
logHint.Size = UDim2.new(1, -24, 0, 18)

local logRow, logButtons = Kit.buttonRow(logModal.Body, {
    {
        text = "清空日志",
        tone = "quiet",
        onClick = function()
            Log.clear()
            App.status("已清空日志。", "info")
        end,
    },
    {
        text = "关闭",
        onClick = function()
            logModal:Close()
        end,
    },
}, { order = 0 })
logRow.Position = UDim2.new(0, 12, 1, -40)
logRow.Size = UDim2.new(1, -24, 0, 30)

local function renderLog()
    for _, child in ipairs(logList:GetChildren()) do
        if child:IsA("TextLabel") then
            child:Destroy()
        end
    end

    local entries = Log.entries
    if #entries == 0 then
        local empty = Kit.label(logList, "还没有记录。导入 OBJ 后会在这里累积状态与错误。", {
            wrap = true,
            size = 11,
            color = THEME.textDim,
        })
        empty.LayoutOrder = 1
        return
    end

    for index, entry in ipairs(entries) do
        local color = THEME.textDim
        if entry.kind == "ok" then
            color = THEME.ok
        elseif entry.kind == "warn" then
            color = THEME.warn
        elseif entry.kind == "error" then
            color = THEME.err
        end
        local label = Kit.label(logList, entry.time .. "  " .. entry.text, {
            wrap = true,
            size = 11,
            color = color,
        })
        label.LayoutOrder = index
    end
    task.defer(function()
        pcall(function()
            logList.CanvasPosition = Vector2.new(0, math.max(0, logList.AbsoluteCanvasSize.Y))
        end)
    end)
end

Log.onAppend = function()
    if logModal.Overlay.Visible then
        renderLog()
    end
end

local dragState = { active = false, pointer = Vector2.new(0, 0), origin = Vector2.new(0, 0) }
local resizeState = { active = false, pointer = Vector2.new(0, 0), size = Vector2.new(0, 0) }

function App.syncShadow()
    if not shadow then
        return
    end
    local factor = uiScale.Scale
    local width = window.Size.X.Offset * factor
    local height = window.Size.Y.Offset * factor
    shadow.Position = UDim2.new(
        0,
        window.Position.X.Offset - 6,
        0,
        window.Position.Y.Offset - 6
    )
    shadow.Size = UDim2.fromOffset(width + 12, height + 12)
    shadow.Visible = window.Visible

    if shadowFar then
        shadowFar.Position = UDim2.new(
            0,
            window.Position.X.Offset - 15,
            0,
            window.Position.Y.Offset - 15
        )
        shadowFar.Size = UDim2.fromOffset(width + 30, height + 30)
        shadowFar.Visible = window.Visible
    end
end

local function clampPosition(x, y)
    local camera = Workspace.CurrentCamera
    local viewport = camera and camera.ViewportSize or Vector2.new(1280, 720)
    local scale = uiScale.Scale
    local width = window.Size.X.Offset * scale
    local keepX = math.min(160, width)
    local lowX = -width + keepX
    local highX = viewport.X - keepX
    local lowY = 0
    local highY = math.max(0, viewport.Y - 48)
    return math.floor(clamp(x, lowX, highX)), math.floor(clamp(y, lowY, highY))
end

function App.scaleWindow()
    local camera = Workspace.CurrentCamera
    local viewport = camera and camera.ViewportSize or Vector2.new(1280, 720)
    local width = math.max(1, window.Size.X.Offset)
    local height = math.max(1, window.Size.Y.Offset)
    local factor = math.min(1, (viewport.X - 32) / width, (viewport.Y - 32) / height)
    uiScale.Scale = clamp(factor, 0.5, 1)
    App.syncShadow()
end

function App.centerWindow()
    local camera = Workspace.CurrentCamera
    local viewport = camera and camera.ViewportSize or Vector2.new(1280, 720)
    local scale = uiScale.Scale
    local x = (viewport.X - window.Size.X.Offset * scale) / 2
    local y = (viewport.Y - window.Size.Y.Offset * scale) / 2
    local finalX, finalY = clampPosition(x, y)
    window.Position = UDim2.fromOffset(finalX, finalY)
    App.syncShadow()
end

local function beginDrag(input)
    if input.UserInputType ~= Enum.UserInputType.MouseButton1
        and input.UserInputType ~= Enum.UserInputType.Touch
    then
        return
    end
    dragState.active = true
    dragState.pointer = Vector2.new(input.Position.X, input.Position.Y)
    dragState.origin = Vector2.new(window.Position.X.Offset, window.Position.Y.Offset)
end

dragSurface.InputBegan:Connect(beginDrag)

UserInputService.InputBegan:Connect(function(input, processed)
    if processed or dragState.active or not window.Visible then
        return
    end
    if input.UserInputType ~= Enum.UserInputType.MouseButton1 then
        return
    end
    local pointer = Vector2.new(input.Position.X, input.Position.Y)
    local scale = uiScale.Scale
    local left = window.Position.X.Offset
    local top = window.Position.Y.Offset
    local right = left + window.Size.X.Offset * scale - 206
    local bottom = top + CONFIG.HEADER_HEIGHT * scale
    if pointer.X >= left and pointer.X <= right
        and pointer.Y >= top and pointer.Y <= bottom
    then
        beginDrag(input)
    end
end)

resizeHandle.InputBegan:Connect(function(input)
    if input.UserInputType ~= Enum.UserInputType.MouseButton1
        and input.UserInputType ~= Enum.UserInputType.Touch
    then
        return
    end
    resizeState.active = true
    resizeState.pointer = Vector2.new(input.Position.X, input.Position.Y)
    resizeState.size = Vector2.new(window.Size.X.Offset, window.Size.Y.Offset)
end)

UserInputService.InputChanged:Connect(function(input)
    if input.UserInputType ~= Enum.UserInputType.MouseMovement
        and input.UserInputType ~= Enum.UserInputType.Touch
    then
        return
    end

    local factor = math.max(0.2, uiScale.Scale)
    local pointer = Vector2.new(input.Position.X, input.Position.Y)

    if dragState.active then
        local delta = pointer - dragState.pointer
        local nextX, nextY = clampPosition(
            dragState.origin.X + delta.X / factor,
            dragState.origin.Y + delta.Y / factor
        )
        window.Position = UDim2.fromOffset(nextX, nextY)
        App.syncShadow()
    elseif resizeState.active then
        local camera = Workspace.CurrentCamera
        local viewport = camera and camera.ViewportSize or Vector2.new(1280, 720)
        local limitX = math.min(CONFIG.WINDOW_MAX.X, viewport.X / factor - 12)
        local limitY = math.min(CONFIG.WINDOW_MAX.Y, viewport.Y / factor - 12)
        local delta = pointer - resizeState.pointer
        local width = clamp(
            resizeState.size.X + delta.X / factor,
            math.min(CONFIG.WINDOW_MIN.X, limitX),
            math.max(limitX, CONFIG.WINDOW_MIN.X)
        )
        local height = clamp(
            resizeState.size.Y + delta.Y / factor,
            math.min(CONFIG.WINDOW_MIN.Y, limitY),
            math.max(limitY, CONFIG.WINDOW_MIN.Y)
        )
        State.windowSize = Vector2.new(math.floor(width), math.floor(height))
        if State.minimized then
            window.Size = UDim2.fromOffset(State.windowSize.X, CONFIG.HEADER_HEIGHT)
        else
            window.Size = UDim2.fromOffset(State.windowSize.X, State.windowSize.Y)
        end
        App.scaleWindow()
        local keepX, keepY = clampPosition(window.Position.X.Offset, window.Position.Y.Offset)
        window.Position = UDim2.fromOffset(keepX, keepY)
        App.syncShadow()
    end
end)

UserInputService.InputEnded:Connect(function(input)
    if input.UserInputType == Enum.UserInputType.MouseButton1
        or input.UserInputType == Enum.UserInputType.Touch
    then
        dragState.active = false
        resizeState.active = false
    end
end)

function App.setMinimized(minimized)
    State.minimized = minimized and true or false
    local collapsed = State.minimized

    tabBar.Instance.Visible = not collapsed
    content.Visible = not collapsed
    statusBar.Visible = not collapsed
    subtitleLabel.Visible = not collapsed

    if collapsed then
        main.Position = UDim2.new(0, 0, 0, 0)
        main.Size = UDim2.new(1, 0, 1, 0)
        window.Size = UDim2.fromOffset(State.windowSize.X, CONFIG.HEADER_HEIGHT)
    else
        main.Position = UDim2.new(0, CONFIG.RAIL_WIDTH, 0, 0)
        main.Size = UDim2.new(1, -CONFIG.RAIL_WIDTH, 1, 0)
        window.Size = UDim2.fromOffset(State.windowSize.X, State.windowSize.Y)
    end

    minimizeButton:SetText(collapsed and "□" or "—")
    App.scaleWindow()
    if App.resetHeaderControls then
        App.resetHeaderControls()
    end
end

function App.setWindowHidden(hidden)
    State.windowHidden = hidden and true or false
    window.Visible = not State.windowHidden
    shadow.Visible = not State.windowHidden
    if shadowFar then
        shadowFar.Visible = not State.windowHidden
    end
    openButton.Visible = State.windowHidden
    openShadow.Visible = State.windowHidden
    if not State.windowHidden then
        App.setMinimized(false)
        window.BackgroundTransparency = 0.35
        safeTween(window, { BackgroundTransparency = 0.02 }, 0.2)
        if App.resetHeaderControls then
            App.resetHeaderControls()
        end
    end
end

minimizeButton:OnClick(function()
    App.setMinimized(not State.minimized)
end)

closeButton:OnClick(function()
    App.setWindowHidden(true)
end)

openButton.MouseButton1Click:Connect(function()
    App.setWindowHidden(false)
end)

logButton:OnClick(function()
    renderLog()
    logModal:Open()
end)

UI.scaleField:OnChanged(App.onTransformChanged)
UI.scaleField:OnCommit(function()
    UI.scaleField:Commit(0.000001, 100000, 1)
    App.onTransformChanged()
end)

UI.thicknessField:OnChanged(App.onTransformChanged)
UI.thicknessField:OnCommit(function()
    UI.thicknessField:Commit(CONFIG.MIN_PART_SIZE, 5, CONFIG.DEFAULT_THICKNESS)
    App.onTransformChanged()
end)

UI.rotationTriple:OnChanged(App.onTransformChanged)
UI.rotationTriple:OnCommit(function()
    UI.rotationTriple:Commit(-360000, 360000, 0)
    App.onTransformChanged()
end)

UI.positionTriple:OnChanged(App.onTransformChanged)
UI.positionTriple:OnCommit(function()
    UI.positionTriple:Commit(-1000000000, 1000000000, 0)
    App.onTransformChanged()
end)

UI.customPivotTriple:OnChanged(App.onTransformChanged)
UI.customPivotTriple:OnCommit(function()
    UI.customPivotTriple:Commit(-1000000000, 1000000000, 0)
    App.onTransformChanged()
end)

UI.targetSizeField:OnCommit(function()
    UI.targetSizeField:Commit(1, CONFIG.MAX_PART_LENGTH, CONFIG.DEFAULT_TARGET_SIZE)
end)

UI.maxEdgeField:OnChanged(function()
    App.updateStats()
    App.onTransformChanged()
end)
UI.maxEdgeField:OnCommit(function()
    UI.maxEdgeField:Commit(1, CONFIG.HARD_MAX_EDGES, CONFIG.DEFAULT_MAX_EDGES, true)
    App.updateStats()
    App.onTransformChanged()
end)

UI.shellThicknessField:OnCommit(function()
    UI.shellThicknessField:Commit(CONFIG.MIN_PART_SIZE, 5, CONFIG.DEFAULT_SHELL_THICKNESS)
end)
UI.shellPlateField:OnCommit(function()
    UI.shellPlateField:Commit(
        CONFIG.MIN_SHELL_PLATE_SIZE,
        CONFIG.MAX_SHELL_PLATE_SIZE,
        CONFIG.DEFAULT_SHELL_PLATE_SIZE
    )
end)
UI.shellBudgetField:OnCommit(function()
    UI.shellBudgetField:Commit(100, CONFIG.MAX_SHELL_BUDGET, CONFIG.DEFAULT_SHELL_BUDGET, true)
end)

tabBar:Select(1)
App.refreshCapabilities()
App.refreshPivotUI()
App.updateStats()
App.setProgress(0)
App.scaleWindow()
App.centerWindow()
App.status("就绪。先读取工作区 OBJ 或粘贴文本，再调参数、预览、生成。", "info")

if not CAPS.readfile then
    App.status("未检测到 readfile：请用「粘贴 OBJ」，或换一个提供 readfile 的执行器。", "warn")
end
if not nativePartCreationOk then
    App.status("Part 创建自检失败：当前环境可能禁止客户端创建 Part。", "error")
end

App.refreshToolStatus()
task.delay(1, function()
    pcall(App.refreshToolStatus)
end)

LocalPlayer.CharacterAdded:Connect(function()
    task.wait(1)
    pcall(App.refreshToolStatus)
end)

task.spawn(function()
    local backpack = LocalPlayer:FindFirstChild("Backpack")
    if not backpack then
        return
    end
    backpack.ChildAdded:Connect(function()
        task.wait(0.1)
        pcall(App.refreshToolStatus)
    end)
    backpack.ChildRemoved:Connect(function()
        task.wait(0.1)
        pcall(App.refreshToolStatus)
    end)
end)

task.spawn(function()
    while gui.Parent do
        pcall(App.scaleWindow)
        task.wait(0.5)
    end
end)

print(string.format("[OBJ Wireframe] UI %s 已加载。", CONFIG.UI_VERSION))
